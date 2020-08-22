import io
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
import concurrent.futures

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
        (0, 0): RIGHT, (1, 0): DOWN, (2, 0): UP, (3, 0): DOWN, (4, 0): DOWN, (5, 0): DOWN, (6, 0): DOWN, (7, 0): DOWN, # A0-7
        (7, 1): DOWN,                                                          # B7
        (2, 4): RIGHT, (3, 4): DOWN, (4, 4): UP, (7, 4): UP,                   # E2, 3, 4, 7
        (3, 10): RIGHT, (4, 10): RIGHT,                                        # K3, 4
        (5, 11): DOWN, (6, 11): RIGHT, (7, 11): UP,                            # L5-7
        (0, 20): DOWN, (1, 20): RIGHT, (2, 20): UP,                            # U0-2
        (1, 23): UP,                                                           # X1
        (0, 25): UP, (2, 25): DOWN, (3, 25): RIGHT                             # Z0, 2, 3
}

walk_head_offsets = [(0, 0), (3, 10), (4, 10)]

body_offsets = [
[0, 1], [1, 1], [2, 1], [3, 1], [4, 1], [5, 1], [6, 1],
[0, 2], [1, 2], [2, 2], [3, 2], [4, 2], [5, 2], [6, 2], [7, 2],
[0, 3], [1, 3], [2, 3], [3, 3], [4, 3], [7, 3],
[5, 5], [6, 5], [7, 5],
[7, 6],
[0, 8], [1, 8], [2, 8],
[3, 11], [4, 11],
[0, 12], [1, 12], [2, 12], [3, 12], [4, 12], [5, 12], [6, 12], [7, 12],
[0, 13], [1, 13], [2, 13], [3, 13], [4, 13], [5, 13], [6, 13], [7, 13],
[0, 14], [1, 14], [2, 14], [3, 14], [4, 14], [5, 14], [6, 14], [7, 14],
[1, 15], [2, 15], [3, 15], [4, 15], [5, 15], [6, 15], [7, 15],
[0, 16], [1, 16], [5, 16], [6, 16], [7, 16],
[6, 17], [7, 17],
[3, 18], [4, 18], [5, 18], [6, 18], [7, 18],
[3, 19], [4, 19], [5, 19], [6, 19], [7, 19],
[4, 20], [5, 20], [6, 20], [7, 20],
[0, 21], [1, 21], [2, 21], [3, 21], [4, 21], [5, 21], [6, 21],
[2, 23], [3, 23], [4, 23], [5, 23], [6, 23], [7, 23],
[0, 24], [1, 24], [2, 24], [3, 24], [4, 24], [5, 24], [4, 25]]

bunny_head_offsets = [[5, 25], [2, 26], [5, 26]]
bunny_body_offsets = [[7, 25], [0, 26], [2, 26], [3, 26], [5, 26], [6, 26]]

unused_offsets = [
[5, 3],  [6, 3],
[0, 4],  [1, 4],  [5, 4],  [6, 4],
[0, 10, 2, 3],  [2, 10, 2, 3],  [4, 10, 2, 3],  [6, 10, 2, 3],  [8, 10, 2, 3],
[0, 13, 3, 3],  [3, 13, 2, 3],  [5, 13, 2, 3],  [7, 13, 2, 3],  [8, 13, 1, 1],  [8, 14, 1, 1],  [8, 15, 1, 1],  [5, 6],  [6, 6],

[5, 7],  [6, 7],  [7, 7],
[3, 8],  [4, 8],  [5, 8],  [6, 8],  [7, 8],
[0, 9],  [1, 9],  [2, 9],  [3, 9],  [4, 9],  [10, 18, 1, 1], [10, 19, 1, 1],  [11, 18, 2, 2],  [13, 18, 3, 2],
[0, 10], [1, 10], [2, 10], [5, 10], [6, 10], [7, 10],
[0, 11], [1, 11], [2, 11],
[0, 30, 1, 1], [0, 31, 1, 1], [1, 30, 1, 1], [0, 31, 1, 1],
[2, 16], [3, 16], [4, 16],
[0, 34, 2, 3], [2, 34, 2, 3], [4, 34, 2, 3], [3, 17], [4, 17], [5, 17],
[0, 37, 2, 3], [2, 37, 2, 3], [4, 37, 2, 3],
[3, 20],
[7, 21],
[0, 22], [1, 22], [2, 22], [3, 22], [4, 22], [5, 22], [6, 22], [7, 22],
[0, 23],
[12, 48, 2, 3], [7, 24],
[1, 25], [12, 51, 1, 1], [13, 51, 1, 1],
[7, 26],
[0, 27], [1, 27], [2, 27], [3, 27], [4, 27], [5, 27], [6, 27], [7, 27]]

_sprite_table = {}
def _populate_sprite_table():
    if not _sprite_table:
        def load_sprite_from_file(file):
            filepath = os.path.join(dir, file)
            sprite = Sprite(filepath)
            if sprite.valid:
                _sprite_table[sprite.name.lower()] = sprite
                _sprite_table[os.path.basename(filepath).split(".")[0]] = sprite  # alias for filename base

        with concurrent.futures.ThreadPoolExecutor() as pool:
            for dir in ['sprites']:
                for file in os.listdir(dir):
                    pool.submit(load_sprite_from_file, file)

def get_sprite_from_name(name, local_random=random):
    _populate_sprite_table()
    name = name.lower()
    if name in ['random', 'randomonhit']:
        return local_random.choice(list(_sprite_table.values()))
    if name == '(default link)':
        name = 'link'
    return _sprite_table.get(name, None)

class Sprite(object):
    default_palette = [255, 127, 126, 35, 183, 17, 158, 54, 165, 20, 255, 1, 120, 16, 157,
                       89, 71, 54, 104, 59, 74, 10, 239, 18, 92, 42, 113, 21, 24, 122,
                       255, 127, 126, 35, 183, 17, 158, 54, 165, 20, 255, 1, 120, 16, 157,
                       89, 128, 105, 145, 118, 184, 38, 127, 67, 92, 42, 153, 17, 24, 122,
                       255, 127, 126, 35, 183, 17, 158, 54, 165, 20, 255, 1, 120, 16, 157,
                       89, 87, 16, 126, 69, 243, 109, 185, 126, 92, 42, 39, 34, 24, 122,
                       255, 127, 126, 35, 218, 17, 158, 54, 165, 20, 255, 1, 120, 16, 151,
                       61, 71, 54, 104, 59, 74, 10, 239, 18, 126, 86, 114, 24, 24, 122]

    default_glove_palette = [246, 82, 118, 3]

    def __init__(self, filename):
        with open(filename, 'rb') as file:
            filedata = bytearray(file.read())
        self.name = os.path.basename(filename)
        self.author_name = None
        self.valid = True
        if len(filedata) == 0x7000:
            # sprite file with graphics and without palette data
            self.sprite = filedata[:0x7000]
            self.palette = list(self.default_palette)
            self.glove_palette = list(self.default_glove_palette)
        elif len(filedata) == 0x7078:
            # sprite file with graphics and palette data
            self.sprite = filedata[:0x7000]
            self.palette = filedata[0x7000:]
            self.glove_palette = filedata[0x7036:0x7038] + filedata[0x7054:0x7056]
        elif len(filedata) == 0x707C:
            # sprite file with graphics and palette data including gloves
            self.sprite = filedata[:0x7000]
            self.palette = filedata[0x7000:0x7078]
            self.glove_palette = filedata[0x7078:]
        elif len(filedata) in [0x100000, 0x200000, 0x400000]:
            # full rom with patched sprite, extract it
            self.sprite = filedata[0x80000:0x87000]
            self.palette = filedata[0xDD308:0xDD380]
            self.glove_palette = filedata[0xDEDF5:0xDEDF9]
        elif len(filedata) in [0x100200, 0x200200, 0x400200]:
            # full headered rom with patched sprite, extract it
            self.sprite = filedata[0x80200:0x87200]
            self.palette = filedata[0xDD508:0xDD580]
            self.glove_palette = filedata[0xDEFF5:0xDEFF9]
        elif filedata.startswith(b'ZSPR'):
            result = self.parse_zspr(filedata, 1)
            if result is None:
                self.valid = False
                return
            (sprite, palette, self.name, self.author_name) = result
            if len(sprite) != 0x7000:
                self.valid = False
                return
            self.sprite = sprite
            if len(palette) == 0:
                self.palette = list(self.default_palette)
                self.glove_palette = list(self.default_glove_palette)
            elif len(palette) == 0x78:
                self.palette = palette
                self.glove_palette = list(self.default_glove_palette)
            elif len(palette) == 0x7C:
                self.palette = palette[:0x78]
                self.glove_palette = palette[0x78:]
            else:
                self.valid = False
        else:
            self.valid = False

    @staticmethod
    def default_link_sprite():
        return get_sprite_from_name('Link')

    def decode8(self, pos):
        arr = [[0 for _ in range(8)] for _ in range(8)]
        for y in range(8):
            for x in range(8):
                position = 1<<(7-x)
                val = 0
                if self.sprite[pos+2*y] & position:
                    val += 1
                if self.sprite[pos+2*y+1] & position:
                    val += 2
                if self.sprite[pos+2*y+16] & position:
                    val += 4
                if self.sprite[pos+2*y+17] & position:
                    val += 8
                arr[y][x] = val
        return arr

    def decode16(self, pos):
        arr = [[0 for _ in range(16)] for _ in range(16)]
        top_left = self.decode8(pos)
        top_right = self.decode8(pos+0x20)
        bottom_left = self.decode8(pos+0x200)
        bottom_right = self.decode8(pos+0x220)
        for x in range(8):
            for y in range(8):
                arr[y][x] = top_left[y][x]
                arr[y][x+8] = top_right[y][x]
                arr[y+8][x] = bottom_left[y][x]
                arr[y+8][x+8] = bottom_right[y][x]
        return arr

    def parse_zspr(self, filedata, expected_kind):
        logger = logging.getLogger('')
        headerstr = "<4xBHHIHIHH6x"
        headersize = struct.calcsize(headerstr)
        if len(filedata) < headersize:
            return None
        (version, csum, icsum, sprite_offset, sprite_size, palette_offset, palette_size, kind) = struct.unpack_from(headerstr, filedata)
        if version not in [1]:
            logger.error('Error parsing ZSPR file: Version %g not supported', version)
            return None
        if kind != expected_kind:
            return None

        stream = io.BytesIO(filedata)
        stream.seek(headersize)

        def read_utf16le(stream):
            "Decodes a null-terminated UTF-16_LE string of unknown size from a stream"
            raw = bytearray()
            while True:
                char = stream.read(2)
                if char in [b'', b'\x00\x00']:
                    break
                raw += char
            return raw.decode('utf-16_le')

        sprite_name = read_utf16le(stream)
        author_name = read_utf16le(stream)

        # Ignoring the Author Rom name for the time being.

        real_csum = sum(filedata) % 0x10000
        if real_csum != csum or real_csum ^ 0xFFFF != icsum:
            logger.warning('ZSPR file has incorrect checksum. It may be corrupted.')

        sprite = filedata[sprite_offset:sprite_offset + sprite_size]
        palette = filedata[palette_offset:palette_offset + palette_size]

        if len(sprite) != sprite_size or len(palette) != palette_size:
            logger.error('Error parsing ZSPR file: Unexpected end of file')
            return None

        return (sprite, palette, sprite_name, author_name)

    def decode_palette(self):
        "Returns the palettes as an array of arrays of 15 colors"
        def array_chunk(arr, size):
            return list(zip(*[iter(arr)] * size))
        def make_int16(pair):
            return pair[1]<<8 | pair[0]

        def expand_color(i):
            return ((i & 0x1F) * 8, (i >> 5 & 0x1F) * 8, (i >> 10 & 0x1F) * 8)

        raw_palette = self.palette
        if raw_palette is None:
            raw_palette = Sprite.default_palette
        # turn palette data into a list of RGB tuples with 8 bit values
        palette_as_colors = [expand_color(make_int16(chnk)) for chnk in array_chunk(raw_palette, 2)]

        # split into palettes of 15 colors
        return array_chunk(palette_as_colors, 15)

    def __hash__(self):
        return hash(self.name)

spritesheets = list()
def get_sprite_name(sprite):
    return sprite.name

def load_spritesheets(args):
    sprite = Sprite(args.rom)
    spritesheets.append(sprite)
    if args.multisprite_simple or args.multisprite_full:
        if args.sprite:
            for x in args.sprite.split(","):
                sprite = get_sprite_from_name(x)
                spritesheets.append(sprite)
        else:
            _populate_sprite_table()
            for sprite in set(_sprite_table.values()):
                spritesheets.append(sprite)
    
    if len(spritesheets) > args.max_sprites:
        spritesheets.sort(key=get_sprite_name)
        random.shuffle(spritesheets)
        while len(spritesheets) > args.max_sprites:
            spritesheets.pop()

    for sprite in spritesheets:
        logging.info("Using sprite %s made by %s", sprite.name, sprite.author_name)

def check_tile(sheet, src):
    # srcoff = base_offsets[off]*0x40 + h*0x200
    srcoff_old = (src[1]*16+src[0])*0x40
    if len(src) == 2:
        src[0] *= 2
        src[1] *= 2
        src.append(2)
        src.append(2)
    for h in range(src[3]):
        for w in range(src[2]):
            srcoff = (src[0] + w) * 0x20 + (src[1] + h) * 0x200
            # logging.info("%d, %d - %d, %d - %d, %d, %d", src[0], src[1], src[2], src[3], srcoff, srcoff_old, len(sheet))
            if sheet[srcoff]:
                return True
    return False

def copy_tile(rom, sheet, src, dst):
    if len(src) == 2:
        src[0] *= 2
        src[1] *= 2
        src.append(2)
        src.append(2)
    if len(dst) == 2:
        dst[0] *= 2
        dst[1] *= 2
        dst.append(2)
        dst.append(2)
    if src[2] != dst[2] or src[3] != dst[3]:
        return # Not safe to overwrite the tile since width/heights don't match
    for h in range(src[3]):
        for w in range(src[2]):
            srcoff = (src[0]+w)*0x20 + (src[1]+h)*0x200
            dstoff = 0x80000 + (dst[0]+w)*0x20 + (dst[1]+h)*0x200
            for z in range(0x20):
                write_byte(rom, dstoff+z, sheet[srcoff+z])



def shuffle_offsets(args, rom, base_offsets, shuffled_offsets, force_use_sprite=False):
    for off in range(len(base_offsets)):
        foundspr = force_use_sprite
        random.shuffle(spritesheets)
        srcsheet = spritesheets[0].sprite
        for sprite in spritesheets:
            if foundspr or check_tile(sprite.sprite, base_offsets[off] if args.multisprite_simple else shuffled_offsets[off]):
                srcsheet = sprite.sprite
                break

        copy_tile(rom, srcsheet, base_offsets[off] if args.multisprite_simple else shuffled_offsets[off], base_offsets[off])

def shuffle_palletes(args, rom):
    offsets = [0, 30, 60, 90]
    shuffled_offsets = offsets.copy()
    if (args.palette):
        random.shuffle(shuffled_offsets)

    for off in range(len(offsets)):
        sprite = random.choice(spritesheets)

        if (args.multisprite_simple):
            srcoff = offsets[off]
        else:
            srcoff = shuffled_offsets[off]

        dstoff = 0xDD308 + offsets[off]
        for w in range(30):
            write_byte(rom, dstoff+w, sprite.palette[srcoff+w])

    if (args.multisprite_simple or args.multisprite_full):
        sprite = random.choice(spritesheets)
        dstoff = 0xDEDF5
        for w in range(4):
            write_byte(rom, dstoff + w, sprite.glove_palette[w])

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

    if (not args.seed):
        args.seed = str(random.randint(0,999999999))

    logger.info('Using Seed ' + args.seed)
    random.seed(int(args.seed))

    rom = bytearray(open(args.rom, 'rb').read())
    load_spritesheets(args)

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

    shuffled_bunny_head_offsets = bunny_head_offsets.copy()
    random.shuffle(shuffled_bunny_head_offsets)

    shuffled_bunny_body_offsets = bunny_body_offsets.copy()
    random.shuffle(shuffled_bunny_body_offsets)

    all_bunny_offsets = bunny_head_offsets + bunny_body_offsets
    shuffled_all_bunny_offsets = all_bunny_offsets.copy()
    random.shuffle(shuffled_all_bunny_offsets)

    if not args.head and not args.body and not args.chaos:
        shuffle_offsets(args, rom, all_offsets, all_offsets)
        shuffle_offsets(args, rom, all_bunny_offsets, all_bunny_offsets)
    elif args.chaos:
        shuffle_offsets(args, rom, all_offsets, shuffled_all_offsets)
        shuffle_offsets(args, rom, all_bunny_offsets, shuffled_all_bunny_offsets)
    else:
        if args.head:
            shuffle_offsets(args, rom, head_offsets_list, shuffled_head_offsets)
            shuffle_offsets(args, rom, bunny_head_offsets, shuffled_bunny_head_offsets)
        if args.body:
            shuffle_offsets(args, rom, body_offsets, shuffled_body_offsets)
            shuffle_offsets(args, rom, bunny_body_offsets, shuffled_bunny_body_offsets)

    #multisprite_simple/multisprite_full shuffle of remaining sprites, forcing the current selection to remain in place AND be used, even if blank.
    shuffle_offsets(args, rom, unused_offsets, unused_offsets, True)
    shuffle_palletes(args, rom)

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
            os.remove(os.path.join(alttpr_sprite_dir, sprite))
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
    parser.add_argument('--palette', help='Shuffle the armour/bunny palettes.', action='store_true')
    parser.add_argument('--sprite', help='Specifies a comma separated list of sprites to use')
    parser.add_argument('--max_sprites', help='Max number of sprites to use for multisprite_* options', type=int, default=3)
    parser.add_argument('--multisprite_simple', help='Choose each sprite randomly from all spritesheets in sprites/ as sources, instead of the current spritesheet in the provided rom. Keep poses unshuffled (i.e. each sprite will be sourced from the same position in a random sprite).', action='store_true')
    parser.add_argument('--multisprite_full', help='Choose each sprite randomly from all spritesheets in sprites/ as sources, instead of the current spritesheet in the provided rom. Shuffle poses according to other args (i.e. each sprite will be sourced from a random position in a random spritesheet according to the other --head/--body/--chaos arguments).', action='store_true')
    parser.add_argument('--chaos', help='Shuffle all head/body sprites among each other. This will look weird.', action='store_true')
    parser.add_argument('--dumpsprites', help='Update ./sprites/alttpr/ with the latest sprites from https://alttpr.com/sprites for use with the --multisprite options.', action='store_true')
    parser.add_argument('--seed', help='Specifies a seed that determines the sprite shuffle process')
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

