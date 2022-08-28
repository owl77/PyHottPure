import copy

def inv(list):
 aux = []
 for x in range(0,len(list)):
   aux.append(list[len(list)-1-x])
 return aux
 
def leq(x,list):
 for y in list:
    if y > x:
     return False
 return True

def join(x,list):
  aux = [] 
  if len(list)==0:
    return [[x]]   
  for y in list:
    aux.append([x] + y)
  return aux     

def DeltaMorph(n,m,passi):
  if n == -1:
    return []    
  aux = []
  for x in range(0,m+1):
      if leq(x,passi):
       y = copy.deepcopy(DeltaMorph(n-1, m, copy.deepcopy(passi+[x])))
       z = join(x,y)
       aux = aux + z       
  return aux 
    
  
def dDeltaMorph(n):
 aux = DeltaMorph(n,n+1,[])

 aux2 = []
 for x in aux:
  ux = list(set(x))
  if len(ux) == n+1:
      aux2.append(x)
 return inv(aux2)               
            
def sDeltaMorph(n):
 if n < 1:
    return []    
 aux = DeltaMorph(n,n-1,[])

 aux2 = []
 for x in aux:
  ux = list(set(x))
  if len(ux) == n:
      aux2.append(x)
 return aux2     
 
def DeltaComp(f,g,n):
 aux = []
 for n in range(0,n+1):
   aux.append(f[g[n]])
 return aux       
     
         
    
                          