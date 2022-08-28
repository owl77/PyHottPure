
import copy
from tokenizer import * 
from parser import * 
import random


def Subset(a,b):
 for x in a:
    if not x in b:
     return False
 return True    

def ListEquals(a,b):
 return Subset(a,b) and Subset(b,a)


def Free(ast,varnames):
 if ast.name=="Leaf":
   if not ast.value in varnames:
    ast.free = True
    return ast
   else:
    ast.free = False
    return ast
 else:
  if ast.operator.value!="lambda":
   oldchildren = ast.children
   ast.children = [Free(x,varnames) for x in oldchildren]
   return ast
  else:
   newnames = varnames + [ast.operator.variable.value]
   oldchildren = ast.children
   ast.children = [Free(x,newnames) for x in oldchildren]
   return ast

def VarSubstitution(ast,oldname,freshname):
 if ast.name=="Leaf":
  if ast.free ==True and ast.value == oldname:
   ast.value = freshname
   return ast
  else:
   return ast
 else:
  oldchildren = ast.children
  ast.children=[VarSubstitution(x,oldname,freshname) for x in oldchildren]
  return ast


def BoundVariableChange(ast,oldname,newname):
 if ast.name=="Leaf":
  return ast
 else:
  if ast.operator.value=="lambda":
   if ast.operator.variable.value==oldname:
    ast.operator.variable.value=newname
    aux = [VarSubstitution(Free(x,[]),oldname,newname) for x in ast.children]
    ast.children = [BoundVariableChange(x,oldname,newname) for x in aux]
    return ast
   else:
    ast.children = [BoundVariableChange(x,oldname,newname) for x in ast.children]  
    return ast
  else:
    ast.children = [BoundVariableChange(x,oldname,newname) for x in ast.children]  
    return ast


def Numeric(ast,n):
 if ast.name=="Leaf":
  return ast
 else:
  if ast.operator.value=="lambda":
   var = ast.operator.variable.value
   ast.operator.variable.value = str(n)
   aux = VarSubstitution(Free(ast.children[0],[]), var, str(n)) 
   ast.children = [Numeric(aux, n+1)]
   return ast
  else:
   aux = [Numeric(x,n) for x in ast.children]
   ast.children = aux
   return ast

def FastEquals(ast1,ast2):
    if ast1.name =="Leaf":
      if ast2.name=="Leaf":
        return ast1.value == ast2.value
    else:
     if ast2.name=="Constructor":      
       if ast1.operator.value != ast2.operator.value:
           return False
       if len(ast1.children)!= len(ast2.children):
           return False
       for x in range(0,len(ast1.children)):
          if not FastEquals(ast1.children[x], ast2.children[x]):
              return False      
       return True
     return False
         
def Equals(ast1,ast2):
  a1 = copy.deepcopy(ast1)
  a2 = copy.deepcopy(ast2)    
  aux1 = Numeric(a1,0)
  aux2 = Numeric(a2,0)
  return FastEquals(aux1,aux2)
  
def BasicSubstitution(ast,old,fresh):
 if ast.name=="Leaf":
    if ast.free!=True:
      return ast    
 if Equals(ast,old):     
   return fresh
 if ast.name=="Leaf":
  return ast
 else:
  oldchildren = ast.children
  ast.children=[BasicSubstitution(x,old,fresh) for x in oldchildren]
  if len(ast.children)==2:
    ast.left = ast.children[0]
    ast.right = ast.children[1]  
  return ast
  

def GetFreeVars(ast):
 if ast.name== "Leaf":
  if ast.free==True and not ast.value in constants:
   return [ast.value]
  else:
   return []
 else:
   aux =[GetFreeVars(x) for x in ast.children]
   aux2 = []
   for x in aux:
    for y in x:
     aux2.append(y)
   return aux2  
 
def GetBindVars(ast):
 if ast.name=="Leaf":
  return []
 else:
  if ast.operator.value =="lambda":
   aux3 = [ast.operator.variable.value]
  else:
   aux3=[]
  aux2 =[GetBindVars(x) for x in ast.children]
  for x in aux2:
   for y in x:
    aux3.append(y) 
  return aux3
 
def Substitution(ast,var,term):
  ast = copy.deepcopy(Free(ast,[]))
  term = Free(term,[])
  free = GetFreeVars(term)
  bind = GetBindVars(ast)
  subs = [x for x in bind if x in free]
  for y in subs:
   y2 = Fresh(variables + constants,alphabet)
   ast = BoundVariableChange(ast,y, y2)
   variables.append(y2)
  return BasicSubstitution(ast,var,term)
  
  
  
def PairSubstitution(ast,varpair,termpair):
 fr = Fresh(variables, alphabet)
 fresh = Leaf(fr,"HottTerm")
 firstt = termpair[0]
 firstvar = varpair[0]
 secondvar = varpair[1]
 secondt = termpair[1]
 aux = Substitution(firstt, secondvar, fresh)
 aux1 = Substitution(ast, firstvar, aux )
 aux2 = Substitution(aux1, secondvar, secondt)
 aux3 = Substitution(aux2, fresh, secondvar)
 return aux3    
  
def TripleSubstitution(ast,vartriple,termtriple):
  fr1 =  Fresh(variables, alphabet)
  fr2 = Fresh(variables + [fr1],alphabet)
  fresh1 = Leaf(fr1,"HottTerm")   
  fresh2 = Leaf(fr2,"HottTerm")
  firstt = termtriple[0]
  firstvar = vartriple[0]
  secondvar = vartriple[1]
  secondt = termtriple[1]
  thirdvar = vartriple[2]
  thirdt = termtriple[2]
  newfirstt1 = Substitution(firstt, secondvar, fresh1)
  newfirstt = Substitution(newfirstt1, thirdvar, fresh2)
  newsecondt = Substitution(secondt, thirdvar,fresh2)
  aux = Substitution(ast,firstvar, newfirstt)
  aux2 = Substitution(aux, secondvar, newsecondt)
  aux3 = Substitution(aux2, thirdvar, thirdt)
  aux4 = Substitution(aux3, fresh1,secondvar)
  aux5 = Substitution(aux4, fresh2, thirdvar)
  return aux5
   
         
         
      
  
  
def Passing(list, func, n):
 if len(list)==0:
  return [[],n]
 if len(list)==1:
  return [[func(list[0],n)[0]], func(list[0],n)[1]]
 else:
  aux = func(list[0],n)
  aux2 = Passing(list[1:], func, aux[1])
  return [[aux[0]]+ aux2[0], aux2[1]]
  
def FreeEquiv(ast1,ast2):
 if type(ast1).__name__=="Leaf":
  if ast1.free!=ast2.free:
    return False 
 else:
   for x in range(0,len(ast1.children)):
     if FreeEquiv(ast1.children[x],ast2.children[x])!=True:
      return False
  
 return True
          
def Position(ast,exp,n):
 
 
 if Equals(ast,exp) and FreeEquiv(ast,exp):
       
  if type(ast).__name__=="Leaf":    
   ast.pos = n
  else:
   ast.operator.pos = n     
  return [ast, n+1]
 else:
  if type(ast).__name__=="Leaf":
   return [ast, n]
  else:
   kinder = copy.deepcopy(ast.children)      
   aux = Passing(kinder, lambda x,y: Position(x,exp,y), n)
   ast.children = aux[0]
   return [ast,aux[1]]
   
    
def BasicSubstitutionByPosition(ast,old,fresh,positions):
    
 if Equals(ast,old):
   if ast.name=="Constructor" and ast.operator.pos in positions:     
    return fresh
   if ast.name!="Constructor" and ast.pos in positions:
     return fresh
 if type(ast).__name__=="Leaf":
  return ast
 else:
  oldchildren = ast.children
  ast.children=[BasicSubstitutionByPosition(x,old,fresh,positions) for x in oldchildren]
  if len(ast.children)==2:
    ast.left = ast.children[0]
    ast.right = ast.children[1]
  return ast
  
def SubstitutionByPosition(ast,term1,term2,positions):
  free = GetFreeVars(term2)
  bind = GetBindVars(ast)
  subs = [x for x in bind if x in free]
  for y in subs:
   y2 = Fresh(variables + constants,alphabet)
   ast = BoundVariableChange(ast,y, y2)
   variables.append(y2)
  return BasicSubstitutionByPosition(Position(ast,term1,0)[0],term1,term2,positions)    
  
  
def IsContextExtension(gamma,gamma2):                   
    if len(gamma2.children) ==0:
     return False
    vartyp = gamma2.children[len(gamma2.children)-1]
    aux2 = copy.deepcopy(gamma2)
    aux2.children = aux2.children[0:len(aux2.children)-1]     
    if Equals(gamma,aux2):    
        return True  
        

def preReparse(l):
 aux = []    
 for x in l:    
  aux.append(HottTerm3(Tokenize(x)))
 return aux       
 
def Reparse(l):
    aux = []
    for x in l:
        aux.append(preReparse(x))
    return aux     
 

    

def Dup1(l):
 for x in range(0,len(l)):
  for y in range(0,len(l)):
     if x!=y and ListEquals(l[x],l[y]):
       l.pop(x)
       return l     
 return l
        
def Dup2(l):
 while len(l)!= len(Dup1(l)):
    l = Dup1(l)
 return l         

     
 
def ListSubset(a,b):
 c = False    
 for x in a:
  for y in b:
    if ListEquals(x,y):
      c = True  
  if c == False:
    return False
  c = False
  
              
 return True
 
def ListListEquals(a,b):
 if len(a)!=len(b):
     return False    
 return ListSubset(a,b) and ListSubset(b,a) 
              
 
 
def MultiSub(ast, varlist,termlist):
    aux = copy.deepcopy(ast)
    for v in range(0,len(varlist)):
      aux = Substitution(aux,varlist[v], termlist[v])
          
    
    return aux 
 
          
            
    
      
             
            
               
  