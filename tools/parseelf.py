#!/usr/bin/env python3

# SPDX-FileCopyrightText: 2023 Ledger SAS
# SPDX-FileCopyrightText: 2025 H2Lab
# SPDX-License-Identifier: Apache-2.0

import sys
import lief
import json

# TODO:
# use argparse for inline documentation
# use Path arg type for arg0 and arg1
# arg0 (i.e. input elf file must exists), arg1 might not (i.e. build from scratch)

# Define basic binary info dict
if __name__ == '__main__':
    binary = lief.parse(sys.argv[1])
    bindict = {'text': {'vaddr':0, 'size':0},
               'data': {'vaddr':0, 'laddr':0, 'size':0},
               'bss': {'vaddr':0, 'size':0}};

    for section in binary.sections:
        if section.name == '.text':
            bindict['text']['vaddr'] = section.virtual_address
            bindict['text']['size'] = section.size
        if section.name == '.ARM':
            # only increment size of text, base addr is set using .text
            bindict['text']['size'] += section.size
        if section.name == '.data':
            bindict['data']['vaddr'] = section.virtual_address
            bindict['data']['laddr'] = binary.get_symbol('_sidata').value
            bindict['data']['size'] = section.size
        if section.name == '.bss':
            bindict['bss']['vaddr'] = section.virtual_address
            bindict['bss']['size'] = section.size
    bindict['text']['vaddr'] = hex(bindict['text']['vaddr'])
    bindict['data']['vaddr'] = hex(bindict['data']['vaddr'])
    bindict['data']['laddr'] = hex(bindict['data']['laddr'])
    bindict['bss']['vaddr'] = hex(bindict['bss']['vaddr'])

    with open(sys.argv[2], 'w') as outfile:
        json.dump(bindict, outfile)

    if len(sys.argv) == 4 and sys.argv[3] == 'dump':
        for key, value in bindict.items():
            print(f"{key}: {value}")
