from os import listdir
from os.path import isfile, join

import sys


mypath = './ghc-master-testsuite-tests-parser/testsuite/tests/parser/should_compile'
pattern = sys.argv[1]


def get_files():
    return [f for f in listdir(mypath) if (isfile(join(mypath, f)) and f.endswith('.hs'))]


def parse_file(hsfile):
    with open(f'ghc-master-testsuite-tests-parser/testsuite/tests/parser/should_compile/{hsfile}', 'r') as f:
        for line in f:
            if pattern in line:
                print(f'./ghc-master-testsuite-tests-parser/testsuite/tests/parser/should_compile/{hsfile}')


if __name__ == '__main__':
    hsfiles = get_files()
    for hsfile in hsfiles:
        parse_file(hsfile)