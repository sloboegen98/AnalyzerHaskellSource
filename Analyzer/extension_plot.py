from matplotlib import pyplot as plt
import numpy as np

from os import listdir
from os.path import isfile, join

# monitor_extensions = ['MonadFailDesugaring']
monitor_extensions = ['FunctionalDependencies', 'TypeFamilies', 'TypeInType']
# monitor_extensions = ['CPP', 'DeriveDataTypeable', 'NoImplicitPrelude', 'OverloadedStrings']
ghc_ver = ['ghc-7.8.3\nDec 2014', 'ghc-7.8.4\nMay 2015', 'ghc-7.10.3\nJan 2016', 'ghc-7.10.3\nJun 2016', 'ghc-8.0.1\nJan 2017', 'ghc-8.0.2\nJun 2017', 'ghc-8.2.2\nJan 2018', 'ghc-8.2.2\nJun 2018', 'ghc-8.6.3\nJan 2019', 'ghc-8.6.5\nJun 2019', 'ghc-8.6.5\nJan 2020', 'ghc-8.8.3\nApr 2020']


reports = 'reports'
files = ['report01.txt', 'report210.txt', 'report501.txt', 'report602.txt', 'report715.txt', 'report817.txt', 'report1003.txt', 'report1112.txt', 'report1301.txt', 'report1325.txt', 'report1420.txt', 'report1508.txt']
lts_size = [827, 1063, 1764, 1993, 1997, 2424, 2665, 2481, 2316, 2352, 2470, 2308]

table = dict()
period = 0

for i, f in enumerate(files):
    period += 1
    for e in monitor_extensions:
        table.setdefault(e, [])
        table[e].append(0)

    all_packages = 0
    
    lines = open(f, 'r')
    for line in lines:
        if (line == ""):
            continue

        line = line.rstrip()
        extension, cnt = line.split()
        all_packages += int(cnt)
        if (extension in monitor_extensions):
            table[extension][i] = int(cnt) / lts_size[i]


x = list(range(1,13))
plt.xticks(x, ghc_ver)
# plt.yticks([i for i in range(19)])

# print(table['NullaryTypeClasses'])

for e in monitor_extensions:
    if e != 'TypeInType':
        plt.plot(x, table[e], label=e, marker='o')
    else:
        plt.plot([np.NaN, np.NaN, np.NaN, np.NaN] + x[4:], table[e], label=e, marker='o')    

# plt.title("Изменение доли пакетов, использующих расширения")
# plt.title("Изменение числа пакетов, использующих расширения")
plt.legend()
plt.show()
