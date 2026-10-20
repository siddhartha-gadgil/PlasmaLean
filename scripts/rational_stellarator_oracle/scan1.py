import sys
from tsim2 import main
f=sys.argv[1]
for (Ib,tq,sw) in [(0.0037,0.3,(0.1,0.1,0.5)),(0.0037,0.5,(0.1,0.1,0.5)),(0.0035,0.3,(0.1,0.1,0.5)),(0.0037,0.3,(0.1,0.1,1.0)),(0.0037,0.3,(0.1,0.1,0.25))]:
    print('==',Ib,tq,sw)
    main(f,1.0e-5,Ib,0.0006,0,tolQ_frac=tq,split_w=sw)
