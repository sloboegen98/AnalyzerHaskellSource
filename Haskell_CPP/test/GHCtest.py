from os import listdir, system
from os.path import isfile, join

import sys


mypath = 'ghc-master-testsuite-tests-parser/testsuite/tests/parser/should_compile/'
# pattern = sys.argv[1]


def get_files():
    return [f for f in listdir(mypath) if (isfile(join(mypath, f)) and f.endswith('.hs'))]


def parse_file(hsfile):
    print('--------------------')
    print(f'parsing {hsfile} ...')
    system(f'../parsertestexe ghc-master-testsuite-tests-parser/testsuite/tests/parser/should_compile/{hsfile}')
    print('--------------------')


if __name__ == '__main__':
    hsfiles = get_files()
    for hsfile in hsfiles:
        parse_file(hsfile)