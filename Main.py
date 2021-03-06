import logging
import argparse
import os
import random
from pathlib import Path
from urllib.request import urlopen
import json
from glob import glob
from urllib.parse import urlparse
import shutil
import struct

__version__ = '0.3'

#Shuffles all of the head and/or body sprites in Link's spritesheet in any randomizer or ALttP JP 1.0 ROM

#Can export a patched ROM or a .zspr file (for use on other .zspr sprite loaders, like
#the http://alttpr.com main site as of v31.0.7) with the --zspr argument.

#Can shuffle heads only with other heads (--head), bodies with only other bodies (--body),
#both heads and bodies but each within their own pool (--head --body), or all head and body
#sprites shuffled in the same pool (--chaos).

#Can also source randomly from all .zspr sprites in the ./sprites/ subfolder, instead of
#sourcing from the spritesheet already present in the provided ROM.  Since this loads
#sprites with the palette they weren't designed with, this will certainly look awful.
#Use the --multisprite_{simple,full} options if you want a frankensprite.  Simple sources
#each destination sprite from the same position in a random spritesheet (ignoring the
#position-altering --head/--body/--chaos args), full sources from random positions in
#random sprites.  You probably won't be able to tell the difference.  Don't use this.

#Sprites are no longer distributed with this script; use the --dumpsprites option to
#update ./sprites/alttpr/ with the latest sprites from https://alttpr.com/sprites
#for use with the --multisprite options.

#Credit goes to Synack for the idea.

#Usage: `python Main.py {--head,--body,--chaos,--multisprite_simple,--multisprite_full,--zspr} --rom lttpromtobepatched.sfc #generates {Frankenspriteshuffled,Spriteshuffled}_{head,body,full,chaos}_lttpromtobepatched.sfc`

#EASY FIRST USAGE: `python Main.py --head --rom lttpromwithsourcespritesheet.sfc --zspr`
#which generates `Spriteshuffled_head_lttpromwithsourcespritesheet.zspr`, a .zspr file with
#Link's head sprites shuffled with each other, which can be used on http://alttpr.com by
#selecting "Load Custom Sprite" after ROM generation.

#General rom patching logic copied from https://github.com/LLCoolDave/ALttPEntranceRandomizer

def write_byte(rom, address, value):
    rom[address] = value

# Tile offsets starting at 0x80000 for all head and body sprites
# These should really be 2D.  Sorry.
#
# This does not include unused offsets, since these are used for
# sprites credits text in many spritesheets, and we don't want
# credits text being shuffled into body positions.  That would
# look bad, and heaven forbid a frankensprite looks bad.
# Source of used/unused offsets:
# https://docs.google.com/document/d/11F14QINktk7f3reGsibIQxp2WRP63j6EYdS3svlliQA/edit
UP = 0
RIGHT = 1
DOWN = 2

# Offset: facing dict, used to keep walk cycle with consistent facing
head_offsets = { # Row from spritesheet commented at the end
        0: RIGHT, 1: DOWN, 2: UP, 3: DOWN, 4: DOWN, 5: DOWN, 6: DOWN, 7: DOWN, # A0-7
        16*1+7: DOWN,                                                          # B7
        16*4+2: RIGHT, 16*4+3: DOWN, 16*4+4: UP, 16*4+7: UP,                   # E2, 3, 4, 7
        16*10+3: RIGHT, 16*10+4: RIGHT,                                        # K3, 4
        16*11+5: DOWN, 16*11+6: RIGHT, 16*11+7: UP,                            # L5-7
        16*20+0: DOWN, 16*20+1: RIGHT, 16*20+2: UP,                            # U0-2
        16*23+1: UP,                                                           # X1
        16*25+0: UP, 16*25+2: DOWN, 16*25+3: RIGHT                             # Z0, 2, 3
}

walk_head_offsets = [0, 16*10+3, 16*10+4]

body_offsets = [
16*1+0, 16*1+1, 16*1+2, 16*1+3, 16*1+4, 16*1+5, 16*1+6,
16*2+0, 16*2+1, 16*2+2, 16*2+3, 16*2+4, 16*2+5, 16*2+6, 16*2+7,
16*3+0, 16*3+1, 16*3+2, 16*3+3, 16*3+4, 16*3+7,
16*5+5, 16*5+6, 16*5+7,
16*6+7,
16*8+0, 16*8+1, 16*8+2,
16*11+3, 16*11+4, 
16*12+0, 16*12+1, 16*12+2, 16*12+3, 16*12+4, 16*12+5, 16*12+6, 16*12+7,
16*13+0, 16*13+1, 16*13+2, 16*13+3, 16*13+4, 16*13+5, 16*13+6, 16*13+7,
16*14+0, 16*14+1, 16*14+2, 16*14+3, 16*14+4, 16*14+5, 16*14+6, 16*14+7,
16*15+1, 16*15+2, 16*15+3, 16*15+4, 16*15+5, 16*15+6, 16*15+7,
16*16+0, 16*16+1, 16*16+5, 16*16+6, 16*16+7,
16*17+6, 16*17+7,
16*18+3, 16*18+4, 16*18+5, 16*18+6, 16*18+7,
16*19+3, 16*19+4, 16*19+5, 16*19+6, 16*19+7,
16*20+4, 16*20+5, 16*20+6, 16*20+7,
16*21+0, 16*21+1, 16*21+2, 16*21+3, 16*21+4, 16*21+5, 16*21+6,
16*23+2, 16*23+3, 16*23+4, 16*23+5, 16*23+6, 16*23+7,
16*24+0, 16*24+1, 16*24+2, 16*24+3, 16*24+4, 16*24+5, 16*25+4]

def shuffle_offsets(args, rom, base_offsets, shuffled_offsets, spritelist, current_sprite):
    for off in range(len(base_offsets)):
        if (args.multisprite_simple or args.multisprite_full):
            foundspr = False
            while (foundspr is False):
                srcpath = random.choice(spritelist)
                srcsheet = srcpath.read_bytes()
                # Z sprite format: little endian pixel offset stored as 4 byte
                # integer at byte 9 of .zspr
                # source: https://docs.google.com/spreadsheets/d/1oNx8IvLcugva0lCqP_VfdalsUppuMiVyFjwBrSGCTiE/edit#gid=0
                baseoff = struct.unpack_from('<i', srcsheet, 9)[0]
                #Scan src region, if blank, pick another sprite
                for tst_h in range(2):
                    if (args.multisprite_simple):
                        srcoff = baseoff + base_offsets[off]*0x40 + tst_h*0x200
                    else:
                        srcoff = baseoff + shuffled_offsets[off]*0x40 + tst_h*0x200
                    for tst_w in range(0x40):
                        if (srcsheet[srcoff+tst_w]):
                            foundspr = True
                            break

        else:
            srcsheet = current_sprite
            baseoff = 0

        for h in range(2): # All shuffled sprites are 2x2 tiles
            if (args.multisprite_simple):
                srcoff = baseoff + base_offsets[off]*0x40 + h*0x200
            else:
                srcoff = baseoff + shuffled_offsets[off]*0x40 + h*0x200

            dstoff = 0x80000 + base_offsets[off]*0x40 + h*0x200

            for w in range(0x40):
                write_byte(rom, dstoff+w, srcsheet[srcoff+w])

# .zspr file dumping logic copied with permission from SpriteSomething:
# https://github.com/Artheau/SpriteSomething/blob/master/source/meta/classes/spritelib.py#L443 (thanks miketrethewey!)
def dump_zspr(rom, outfilename):
    sprite_sheet = rom[0x80000:0x87000]
    palettes = rom[0xdd308:0xdd380]
    # Add glove data
    palettes.extend(rom[0xdedf5:0xdedf9])
    HEADER_STRING = b"ZSPR"
    VERSION = 0x01
    SPRITE_TYPE = 0x01  # this format has "1" for the player sprite
    RESERVED_BYTES = b'\x00\x00\x00\x00\x00\x00'
    QUAD_BYTE_NULL_CHAR = b'\x00\x00\x00\x00'
    DOUBLE_BYTE_NULL_CHAR = b'\x00\x00'
    SINGLE_BYTE_NULL_CHAR = b'\x00'

    write_buffer = bytearray()

    write_buffer.extend(HEADER_STRING)
    write_buffer.extend(struct.pack('B', VERSION)) # as_u8
    checksum_start = len(write_buffer)
    write_buffer.extend(QUAD_BYTE_NULL_CHAR) # checksum
    sprite_sheet_pointer = len(write_buffer)
    write_buffer.extend(QUAD_BYTE_NULL_CHAR)
    write_buffer.extend(struct.pack('<H', len(sprite_sheet))) # as_u16
    palettes_pointer = len(write_buffer)
    write_buffer.extend(QUAD_BYTE_NULL_CHAR)
    write_buffer.extend(struct.pack('<H', len(palettes))) # as_u16
    write_buffer.extend(struct.pack('<H', SPRITE_TYPE)) # as_u16
    write_buffer.extend(RESERVED_BYTES)
    # sprite.name
    write_buffer.extend(outfilename.encode('utf-16-le'))
    write_buffer.extend(DOUBLE_BYTE_NULL_CHAR)
    # author.name
    write_buffer.extend("ALttPLinkSpriteShuffler".encode('utf-16-le'))
    write_buffer.extend(DOUBLE_BYTE_NULL_CHAR)
    # author.name-short
    write_buffer.extend("SpriteShuffler".encode('ascii'))
    write_buffer.extend(SINGLE_BYTE_NULL_CHAR)
    write_buffer[sprite_sheet_pointer:sprite_sheet_pointer +
                 4] = struct.pack('<L', len(write_buffer)) # as_u32
    write_buffer.extend(sprite_sheet)
    write_buffer[palettes_pointer:palettes_pointer +
                 4] = struct.pack('<L', len(write_buffer)) # as_u32
    write_buffer.extend(palettes)

    checksum = (sum(write_buffer) + 0xFF + 0xFF) % 0x10000
    checksum_complement = 0xFFFF - checksum

    write_buffer[checksum_start:checksum_start +
                 2] = struct.pack('<H', checksum) # as_u16
    write_buffer[checksum_start + 2:checksum_start +
                 4] = struct.pack('<H', checksum_complement) # as_u16

    with open('%s' % outfilename, "wb") as zspr_file:
        zspr_file.write(write_buffer)

def shuffle_sprite(args):
    logger = logging.getLogger('')

    if (args.multisprite_simple or args.multisprite_full):
        prefix = "Frankenspriteshuffled"
    else:
        prefix = "Spriteshuffled"

    if (args.chaos):
        prefix += "_chaos"
    elif (args.head and args.body):
        prefix += "_full"
    elif (args.head):
        prefix += "_head"
    elif (args.body):
        prefix += "_body"
    else:
        logger.info('error, no shuffle specified')
        return

    if (args.zspr):
        origromname = os.path.basename(args.rom)
        shortname = os.path.splitext(origromname)[0]
        outfilename = '%s_%s.zspr' % (prefix, shortname)

        logger.info("Creating .zspr file: " + outfilename)
    else:
        outfilename = '%s_%s' % (prefix, os.path.basename(args.rom))

        logger.info("Creating patched ROM: " + outfilename)

    rom = bytearray(open(args.rom, 'rb').read())

    current_sprite = bytearray(28672)

    for i in range(28672):
        current_sprite[i] = rom[0x80000+i]

    head_offsets_list = list(head_offsets.keys())
    shuffled_head_offsets = head_offsets_list.copy()
    random.shuffle(shuffled_head_offsets)

    # Link's walk cycle uses heads A0, K3, and K4 changing every couple frames;
    # if these are swapped with any random head facing any random direction,
    # the result is usually gibberish.  To make this look a bit nicer, this
    # code picks a random direction, then ensures all 3 frames of Link's
    # left/right head walk cycle are facing the same direction.
    #
    # See https://github.com/krelbel/ALttPLinkSpriteShuffler/issues/1
    nonwalk_head_offsets = [i for i in head_offsets_list if i not in walk_head_offsets]
    random_facing = random.randint(0,2)

    for walk_head_offset in walk_head_offsets:
        off = head_offsets_list.index(walk_head_offset)
        shuffled_pose = shuffled_head_offsets[off]

        if head_offsets[shuffled_pose] != random_facing:
            # Exchange this element in shuffled_head_offsets that will end
            # up at this frame of the walking animation with one facing the
            # consistent direction

            while True:
                swap_pose = random.choice(nonwalk_head_offsets)
                swap_off = head_offsets_list.index(swap_pose)
                shuffled_swap_pose = shuffled_head_offsets[swap_off]
                if head_offsets[shuffled_swap_pose] == random_facing:
                    tmp = shuffled_head_offsets[off]
                    shuffled_head_offsets[off] = shuffled_head_offsets[swap_off]
                    shuffled_head_offsets[swap_off] = tmp
                    break

        shuffled_pose = shuffled_head_offsets[off]

    shuffled_body_offsets = body_offsets.copy()
    random.shuffle(shuffled_body_offsets)

    all_offsets = head_offsets_list + body_offsets
    shuffled_all_offsets = all_offsets.copy()
    random.shuffle(shuffled_all_offsets)

    spritelist = list()
    if (args.multisprite_simple or args.multisprite_full):
        for path in Path('./sprites/').rglob('*.zspr'):
            spritelist.append(path)

    if (args.head):
        shuffle_offsets(args, rom, head_offsets_list, shuffled_head_offsets, spritelist, current_sprite)

    if (args.body):
        shuffle_offsets(args, rom, body_offsets, shuffled_body_offsets, spritelist, current_sprite)
    
    if (args.chaos):
        shuffle_offsets(args, rom, all_offsets, shuffled_all_offsets, spritelist, current_sprite)

    if (args.zspr):
        dump_zspr(rom, outfilename)
    else:
        with open('%s' % outfilename, 'wb') as outfile:
            outfile.write(rom)

    logger.info('Done.')

    return

# Sprite dumping logic copied from
# https://github.com/Berserker66/MultiWorld-Utilities/blob/doors/source/classes/SpriteSelector.py
def dump_sprites(args):
    logger = logging.getLogger('')
    alttpr_sprite_dir = "./sprites/alttpr"
    successful = True

    if not os.path.isdir(alttpr_sprite_dir):
        os.makedirs(alttpr_sprite_dir)

    try:
        logger.info("Downloading alttpr sprites list")
        with urlopen('https://alttpr.com/sprites') as response:
            sprites_arr = json.loads(response.read().decode("utf-8"))
    except Exception as e:
        logger.info("Error getting list of alttpr sprites. Sprites not updated.\n\n%s: %s" % (type(e).__name__, e))
        successful = False
        return
 
    try:
        logger.info("Determining needed sprites")
        current_sprites = [os.path.basename(file) for file in glob(os.path.join(alttpr_sprite_dir,"*"))]
        alttpr_sprites = [(sprite['file'], os.path.basename(urlparse(sprite['file']).path)) for sprite in sprites_arr]
        needed_sprites = [(sprite_url, filename) for (sprite_url, filename) in alttpr_sprites if filename not in current_sprites]
 
        alttpr_filenames = [filename for (_, filename) in alttpr_sprites]
        obsolete_sprites = [sprite for sprite in current_sprites if sprite not in alttpr_filenames]
    except Exception as e:
        logger.info("Error Determining which sprites to update. Sprites not updated.\n\n%s: %s" % (type(e).__name__, e))
        successful = False
        return
 
    updated = 0
    for (sprite_url, filename) in needed_sprites:
        try:
            logger.info("Downloading needed sprite %g/%g" % (updated + 1, len(needed_sprites)))
            target = os.path.join(alttpr_sprite_dir, filename)
            with urlopen(sprite_url) as response, open(target, 'wb') as out:
                shutil.copyfileobj(response, out)
        except Exception as e:
            logger.info("Error downloading sprite. Not all sprites updated.\n\n%s: %s" % (type(e).__name__, e))
            successful = False
        updated += 1
 
    deleted = 0
    for sprite in obsolete_sprites:
        try:
            logger.info("Removing obsolete sprite %g/%g" % (deleted + 1, len(obsolete_sprites)))
            os.remove(os.path.join(self.alttpr_sprite_dir, sprite))
        except Exception as e:
            logger.info("Error removing obsolete sprite. Not all sprites updated.\n\n%s: %s" % (type(e).__name__, e))
            successful = False
        deleted += 1

    if successful:
        resultmessage = "alttpr sprites updated successfully"

    return

def main(args):
    if args.dumpsprites:
        dump_sprites(args)
    else:
        shuffle_sprite(args)

if __name__ == '__main__':
    parser = argparse.ArgumentParser(formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    parser.add_argument('--loglevel', default='info', const='info', nargs='?', choices=['error', 'info', 'warning', 'debug'], help='Select level of logging for output.')
    parser.add_argument('--rom', help='Path to a lttp rom to use as the base spritesheet.')
    parser.add_argument('--zspr', help='Output a .zspr instead of a patched rom, convenient for use in other sprite loaders (like the one on alttpr.com)', action='store_true')
    parser.add_argument('--head', help='Shuffle head sprites among each other.', action='store_true')
    parser.add_argument('--body', help='Shuffle body sprites among each other.', action='store_true')
    parser.add_argument('--multisprite_simple', help='Choose each sprite randomly from all spritesheets in sprites/ as sources, instead of the current spritesheet in the provided rom. Keep poses unshuffled (i.e. each sprite will be sourced from the same position in a random sprite).', action='store_true')
    parser.add_argument('--multisprite_full', help='Choose each sprite randomly from all spritesheets in sprites/ as sources, instead of the current spritesheet in the provided rom. Shuffle poses according to other args (i.e. each sprite will be sourced from a random position in a random spritesheet according to the other --head/--body/--chaos arguments).', action='store_true')
    parser.add_argument('--chaos', help='Shuffle all head/body sprites among each other. This will look weird.', action='store_true')
    parser.add_argument('--dumpsprites', help='Update ./sprites/alttpr/ with the latest sprites from https://alttpr.com/sprites for use with the --multisprite options.', action='store_true')
    args = parser.parse_args()

    if not args.dumpsprites:
        if args.rom is None:
            input('No rom specified. Please run with -h to see help for further information. \nPress Enter to exit.')
            exit(1)
        if ((args.head != True) and (args.body != True) and (args.chaos != True)):
            input('No shuffle specified. Please run with -h to see help for further information. \nPress Enter to exit.')
            exit(1)
        if not os.path.isfile(args.rom):
            input('Could not find valid rom for patching at path %s. Please run with -h to see help for further information. \nPress Enter to exit.' % args.rom)
            exit(1)

    # set up logger
    loglevel = {'error': logging.ERROR, 'info': logging.INFO, 'warning': logging.WARNING, 'debug': logging.DEBUG}[args.loglevel]
    logging.basicConfig(format='%(message)s', level=loglevel)

    main(args)

