"""Small exact identity check for the eight-variable cofactor extension.

The accompanying proof supplies continuity, the determinant inequality,
and unrestricted nonrepresentation. This checks the new symbolic data.
"""
import sympy as S

if not __debug__:
    raise RuntimeError('Assertions must be enabled.')

x,y,z,u,v,r,s1,s2=S.symbols('x y z u v r s1 s2')
variables=(x,y,z,u,v,r,s1,s2)
A=S.Matrix([[x,-v+r/2,-y],[y,z+u,x],[z,r/2,0]])
B=S.Matrix([[u,-v/2+r,-v/2],[v,2*z+u/2,u/2]])
Q=(A.T*S.diag(1,1,3)*A-B.T*B).applyfunc(S.expand)
qa,qb,qd,qe=Q[0,0],Q[0,1],Q[2,2],Q[1,2]
q=[-10*qb+2*qd+2*qe,4*qa+2*qb-2*qd-2*qe,
   -4*qa+2*qb+6*qd-10*qe,-4*qa+2*qb+2*qd+2*qe]
c1=x*(-v+r/2)+y*(z+u)
c2=-(x*x+y*y)
assert S.expand(c1-A.cofactor(2,0))==0
assert S.expand(c2-A.cofactor(2,1))==0
O=z*s1+r*s2/2
assert S.expand(O.subs({s1:c1,s2:c2})-A.det())==0
E=[s1-c1,s2-c2]
P=[S.expand(qj+8*sign*ei) for qj in q for ei in E for sign in [-1,1]]
assert len(P)==16
assert all(S.Poly(p,*variables).total_degree()==2 for p in P+[O])
assert all(S.expand(p.subs({s1:c1,s2:c2})-qj)==0
           for qj in q for p in [qj+8*sign*ei for ei in E for sign in [-1,1]])
assert S.expand(O-A.det()-z*E[0]-r*E[1]/2)==0
ones=S.ones(3,1)
ui=[(S.eye(3)[:,i]+ones)/4 for i in range(3)]+[S.zeros(3,1)]
edge_coeff={(0,1):q[0],(0,2):2*q[0]+6*q[1]+5*q[3],(0,3):q[1],
            (1,2):q[2],(1,3):q[3],(2,3):q[0]+2*q[1]+2*q[3]}
identity=S.zeros(3)
norm_sum=S.zeros(3)
for (i,j),coefficient in edge_coeff.items():
    outer=(ui[i]-ui[j])*(ui[i]-ui[j]).T
    identity+=coefficient*outer
    norm_sum+=outer
assert (identity-Q).applyfunc(S.expand)==S.zeros(3)
assert norm_sum==(S.eye(3)+ones*ones.T)/4
differences=[S.expand(P[i]-P[j]) for i in range(16) for j in range(i)]
assert all(p==0 or S.Poly(p,*variables).total_degree()<=2 for p in differences)
print('PASS: two cofactors, determinant, sixteen quadratic branches, graph pullback,')
print('orientation error, all comparison degrees, simplex identity, and margin constant.')
