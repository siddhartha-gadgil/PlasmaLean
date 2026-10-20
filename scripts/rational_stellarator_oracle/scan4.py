import sys
from tsim2 import main
f=sys.argv[1]
for d in [float(x) for x in sys.argv[2:]]:
    print('== delta',d)
    main(f,d,0.0037,0.0006,0,tolQ_frac=0.3,split_w=(0.1,0.1,0.125),faces=False)
