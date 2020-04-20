#! /bin/python3

import sys
import re

with open(sys.argv[1], 'r') as cabalfile:
    data = cabalfile.read()

splitted = list(filter(None, re.split("[ ,]", data)))
cabal = list(filter(lambda w: w != '' and w != ',' and w != ' ', splitted))
res = list(map(lambda w : w.rstrip(' \n'), cabal))

ext = False
package = (sys.argv[2]).rstrip(' \n')

used_ext = set()

for s in res:
    if (s == 'default-extensions:' or s == 'other-extensions:' or s == 'extensions:'):
        ext = True
    elif (len(s) != 0 and (s[0].islower() or s[-1] == ':' or s[0] == '\n')):
        ext = False
    elif ext:
        used_ext.add(s)

ans = filter(lambda e : len(e) > 0 and e[0].isupper(), used_ext)


full_report = sys.argv[3]
with open(full_report, 'a') as f:
    for e in ans:
        if '\n' not in e:
            f.write(e + ' ' + package + '\n')