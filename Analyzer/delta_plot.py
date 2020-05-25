from matplotlib import pyplot as plt
from collections import Counter


files = ['report01.txt', 'report210.txt', 'report501.txt', 'report602.txt', 'report715.txt', 'report817.txt', 'report1003.txt', 'report1112.txt', 'report1301.txt', 'report1325.txt', 'report1420.txt', 'report1508.txt']
ghc_ver = ['ghc-7.8.4', 'ghc-7.10.3', 'ghc-7.10.3', 'ghc-8.0.1', 'ghc-8.0.2', 'ghc-8.2.2', 'ghc-8.2.2', 'ghc-8.6.3', 'ghc-8.6.5', 'ghc-8.6.5', 'ghc-8.8.3']
# ghc_ver = ['ghc-7.8.3', 'ghc-7.8.4', 'ghc-7.10.3', 'ghc-7.10.3', 'ghc-8.0.1', 'ghc-8.0.2', 'ghc-8.2.2', 'ghc-8.2.2', 'ghc-8.6.3', 'ghc-8.6.5', 'ghc-8.6.5', 'ghc-8.8.3']

delta = dict()
prev_value = Counter()


for i, f in enumerate(files):
    lines = open(f, 'r')

    for line in lines:
        line = line.rstrip()
        ext, cnt = line.split()

        if ext not in delta.keys():
            delta.setdefault(ext, [])

        delta[ext].append(int(cnt) - prev_value[ext])

        prev_value[ext] = int(cnt)

x = list(range(1,12))
y = dict()

plt.xticks(x, ghc_ver)

for e, v in delta.items():
    if (len(v) == 12):
        will_be = False
        for d in v:
            if (abs(d) > 100):
                will_be = True

        if will_be:
            y.setdefault(e, v)
            y[e] = v


for e in y.keys():
    # if e in ['CPP', 'OverloadedStrings', 'DeriveDataTypeable']:
    #     plt.plot(x, y[e], label=e)
    # else:
    plt.plot(x, y[e][1:], label=e)

plt.title("Delta")
plt.legend()
plt.show()
