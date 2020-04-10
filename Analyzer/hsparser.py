import sys
import re

hsfile = open(sys.argv[1], 'r')
package = sys.argv[2]

for line in hsfile:
    line.rstrip()
    reg = re.match(r'{-# LANGUAGE (?P<name>[a-zA-Z]+) #-}', line, flags=re.IGNORECASE)
    try:
        extension = reg.groupdict()['name']
        with open('full_list.txt', 'a') as f:
            f.write(extension + ' ' + package + '\n')
    except:
        pass
