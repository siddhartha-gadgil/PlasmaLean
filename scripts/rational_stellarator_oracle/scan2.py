import sys
from tsim2 import main
f=sys.argv[1]
for sw in [(0.1,0.1,0.125),(0.1,0.1,0.0625),(0.1,0.1,0.03)]:
    print('==',sw)
    main(f,1.0e-5,0.0037,0.0006,0,tolQ_frac=0.3,split_w=sw)
