#Sagemath 9.5 code related to AFE1 and its corollary.

#
## definitions 
#

print('Code for Corollary 0.3 of AFE of the first kind\n')

g=euler_gamma
g1=1413472/100000
H=3*10**12

#defs for t0 under first zero
t0=g1 #set t0=H to verify the other value 
C(x)=(x+1/pi*(1/t0+1)*(log(1+1/(2*pi*x))+g-psi(1-1/(2*pi*x))-1/2-1/(2*(1+1/(2*pi*x)))))
c2=1-1/(2*(int(t0)+1))
N0 = int(t0)
c3 = (N0+1/2)/t0
c4 = (N0+3/2)/(N0+1)

#
##verification procedures
#

print('verification procedures for the inequalities verified numerically')
print('-'*10)
f= derivative(C(x),x)
C1(x) = (x+1/pi*(1/t0+1)*(-1/(2*pi*x+1)-psi(1,1-1/(2*pi*x))/(2*pi*x)-pi*x/(2*pi*x+1)^2     ))
#plot(C1(x),(x,1/2,2)).show() #uncomment to visualize C1 and C`(x)*x, which are equal
#plot(x*f,(x,1/2,2)).show()

#uncomment next line to visualize inequality: plot must be positive
#plot(C(x)-C1(x),(x,1/2,2)).show()

#uncomment to show algebragic computations of derivatives
#(x*derivative(log(1+1/(2*pi*x)))).full_simplify()
#(x*derivative(-psi(1-1/(2*pi*x)),x)).full_simplify()
#(x*derivative(-1/(2*(1+1/(2*pi*x))),x)).factor()

one=RIF((1-1/30,1))
#print(n(C1(1)),n(C(1)))
diff=RIF(C(one)-C1(one))
#print(diff)
#print("contains zero?",diff.contains_zero())
#print()
print('verifying that C(x)-x*C\'(x)>0 on (1-1/30,1) with interval arithmetic:',diff>0)

#verifying that C is increasing on (1,1+0.5/6)
print('verifying that C´(x) is positive on (1,1+0.5/6) with interval arithmetic')
one1=RIF((1,65/60))
#print('floating point derivative values at endpoints:', n(f(x=1)),n(f(x=65/60)))
value = RIF(f(x=one1))
#print(value)
#print("is  C´(x) close to zero?",value.contains_zero())
print("is  C´(x) bigger than zero?",value>0)

#
## showing constants (floating point)
#
print('\n'+'-'*10)
print('Constants for Corollary 0.3 of AFE of the first kind.')
print('constant c0 valid for t>=',n(t0), 't=n+1/2:',n(C(1)))
print('constant c0 valid for t>=',n(t0), 'real t:',max( n(C(c2)/c2),n(C(c3)),n(C(c4))))

#defs for t0 the height of RH verification
t0=H #set t0=H to verify the other value 
C(x)=(x+1/pi*(1/t0+1)*(log(1+1/(2*pi*x))+g-psi(1-1/(2*pi*x))-1/2-1/(2*(1+1/(2*pi*x)))))
c2=1-1/(2*(int(t0)+1))
N0 = int(t0)
c3 = (N0+1/2)/t0
c4 = (N0+3/2)/(N0+1)

print('constant c0 valid for t>=',n(t0), 't=n+1/2:',n(C(1)))
print('constant c0 valid for t>=',n(t0), 'real t:',max( n(C(c2)/c2),n(C(c3)),n(C(c4))))