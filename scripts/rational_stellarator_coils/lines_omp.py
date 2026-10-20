exec(open('lines_dictionary_fit.py').read().split("A=np.stack")[0])
A=np.stack([line_field(X,p,u).reshape(-1) for p,u in good],1)
b=target.reshape(-1)
sel=[]; r=b.copy()
An=A/np.linalg.norm(A,axis=0)
for k in range(80):
    j=int(np.argmax(np.abs(An.T@r)))
    sel.append(j)
    c,*_=np.linalg.lstsq(A[:,sel],b,rcond=None)
    r=b-A[:,sel]@c
    if k%5==4: print(k+1, np.linalg.norm(r.reshape(-1,3),axis=1).max(), np.abs(c).max())
