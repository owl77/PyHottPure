from tokenizer import * 
import copy

class Leaf:
 def __init__(self, value,type):
  self.name = "Leaf"
  self.type = type
  self.value = value
  self.free = True
  self.pos = -1
  self.variable = None
class Constructor:
  def __init__(self,operator, type,children):     
   self.name ="Constructor"
   self.operator = operator
   self.type= type
   self.children = children
   self.left = None
   self.right = None
   if len(children)==2:
    self.binary =True
    self.left = children[0]
    self.right = children[1]
    
def Star(parser,separator):
 def out(exp):
  parse = parser(exp)      
  if parse!=None:
   return [parse]  
  if len(exp) < 3:
   return None
  for i in range(0,len(exp)-1):  
    par1 =  parser(exp[0:i])   
    if par1== None:
     continue
    if not exp[i] in separator:
     continue
    par2 =  Star(parser,separator)(exp[i+1:])
    if par2 == None:
     continue
    return [par1] + par2
 return out
 
def ConsStar(parser,separator,value,type):
  def out2(exp):
   op = Leaf(value,type)
   aux = Star(parser,separator)(exp)
   if aux != None:
    return Constructor(op, type, aux)       
  return out2

def Binary(parser1,parser2, opparser):
  def out(exp):
   if len(exp) < 3:
    return None
   for i in range(1,len(exp)-1):
    opars = opparser([exp[i]])      
    if opars ==None:
      continue
    par1 =  parser1(exp[0:i])
    if par1== None:
      continue
    par2 =  parser2(exp[i+1:len(exp)])
    if par2 == None:
       continue
    aux = Constructor(opars, opars.type,[par1,par2])
    return aux
  return out 
  
def Operator(opparser, parser,separator,parenthesis,arity):
 if parenthesis==True:
  def out(exp):
   if len(exp) < 4:
    return None
   for i in range(1,len(exp)-2):
    if  exp[i]!="(" or exp[len(exp)-1]!=")":
     continue
    opars =  opparser(exp[0:i])
    if opars == None:
        continue
    star = Star(parser,separator)(exp[i+1:len(exp)-1])
    if star == None or len(star) !=arity:
     continue    
    return Constructor(opars, opars.type,star)
  return out
 else:
  def out(exp):
   if len(exp) < 2:
    return 
   for i in range(1,len(exp)):
    aux1 = copy.deepcopy(exp)   
    opars = opparser(aux1[0:i])
    if opars == None:
        continue
    star = Star(parser,separator)(aux1[i:])
    if star == None or len(star) !=arity:
        continue
    return Constructor(opars, opars.type,star)
  return out
  
  
def Simple(list, type):
 def out(exp):
  if len(exp)!=1:
    return None
  if exp[0] in list:
   return Leaf(exp[0], type)
 return out  
  
  
def SimpleCons(dic):
 def out(exp):
  if len(exp)!=1:
   return None
  if exp[0] in dic.keys():
   aux = Leaf(exp[0],dic[exp[0]]["targettype"])
   return aux
 return out  
 
 
def BinderParser(binders,variableparser):
 def out(exp):     
  if len(exp) < 3 or len(exp) > 3:
   return None
  if exp[0] in binders.keys() and variableparser([exp[1]])!=None and exp[2]==".":       
   aux = Leaf(exp[0], binders[exp[0]]["targettype"])
   aux.variable = variableparser([exp[1]])
  
   return aux
 return out
  
def Or(parserlist):
   def out(exp):
    for i in range(0,len(parserlist)):
      par =  parserlist[i](exp) 
      if par!=None:
        return par
   return out
  


   
global variables 
variables =["*", "x","y","z","u","w","a","b","c","d","e","f","p","A","B","C","D","E","F"] 
global constants
constants =[ "Nat","U0","O", "succ", "0", "I", "Pi", "Path", "Lambda", "Sigma","pair", "ind", "equals", "plus","inl","inr", "refl"," subpoly"] 


#comp (lambda i. A) \phi (lambda i. u) a_0

 

global initvars
initvars = copy.deepcopy(variables)
global initconsts 

initconsts = copy.deepcopy(constants)


app = {"app":{  "targettype":"HottTerm" } }
binder ={ "lambda":{"targettype":"HottTerm"   }}
vartyping = {":":{"targettype":"VarTyp"}}
gentyping = {":":{"targettype":"GenTyp"}}
equivtyp = {":":{"targettype":"EquivTyp"}}
typing = {"|-":{"targettype":"Typing"}}
equivterm = {"equiv":{"targettype":"EquivTerm"}}
equiv = {"|-":{"targettype":"Equiv"}}


 
def Star2(parser):
 def out(exp):
   for i in range(1,len(exp)):
    aux2 = parser(exp[len(exp)-i:])
    if aux2== None:
     continue
    aux3 = parser(exp[0:len(exp)-i])
    if aux3== None:
     continue
    return [aux3, aux2]        
 return out      
 

 
def HottTerm2(exp):
   global constants
   global variables
   if len(exp)==0:
    return None
   var =  Simple(variables + constants,"HottTerm")(exp)
   if var!= None:
     return var
   
 #  if exp[0] == "subpoly":
  #   if len(exp) > 1:  
   #   aux = Star(HottTerm2,",")(exp[1:])
#     else:
 #     aux = [] 
  #   op = Leaf("subpoly", "HottTerm")
   #  aux2 = Constructor(op, "HottTerm", aux)
    # return aux2
         
        
     
   aux = Star2(HottTerm2)(exp)
   if aux!=None: 
    return aux
   aux = Operator(BinderParser(binder,Simple(variables,"HottTerm")), HottTerm2 ,[","],False,1)(exp)
   if aux!=None:
     return aux
   
   
   if  exp[0]=="(" and exp[len(exp)-1]==")" :
     return HottTerm2(exp[1:len(exp)-1])   
   
   
def Convert(ast):
 if ast==None:
    return None    
 
    
 if type(ast).__name__=="Leaf":
   return ast
 if type(ast).__name__=="Constructor":
  # if ast.operator.value!="subpoly":
   # return Constructor(ast.operator, ast.type, [Convert(copy.deepcopy(ast.children))])
   #else:
    aux1 = copy.deepcopy(ast.children)
    aux2 = [Convert(x) for x in aux1]
    return  Constructor(ast.operator, ast.type, aux2)  
       
 if len(ast)==1:
  return Convert(ast[0])
 first = ast[0: len(ast)-1]
 second = ast[len(ast)-1]
 app = Leaf("app","HottTerm")
 return Constructor(app, "HottTerm", [Convert(first), Convert(second) ])
     

def HottTerm3(exp):
 global variables    
 return Convert(HottTerm2(exp))
 
def VarTyp(exp):
    return Binary( Simple(variables,"HottTerm")   ,HottTerm3 , SimpleCons(vartyping))(exp)        
    
    
def split(e):
     if len(e) == 0:
         return []
     for n in range(0,len(e)):
        if e[n] ==",":
          
              
          return [VarTyp(e[0:n])] + split(e[n+1:])
     return [VarTyp(e)]    
    
    
    
def Context(exp):
    if "|-" in exp:
     return
    if len(exp) == 1 and exp[0]==".":
     return Constructor(Leaf("ctx","Context"),"Context",[])  
  
    aux = split(exp)                  
    return Constructor(Leaf("ctx","Context"),"Context",aux)  
       
#    return ConsStar(VarTyp,",","ctx", "Context")(exp)
    
   
    
def GenTyp(exp):
      return Binary( HottTerm3   ,HottTerm3 , SimpleCons(gentyping))(exp)          
def EquivTerm(exp):
      return Binary( HottTerm3   ,HottTerm3 , SimpleCons(equivterm))(exp)   
def EquivTyp(exp):
       return Binary( EquivTerm   ,HottTerm3 , SimpleCons(equivtyp))(exp) 
def Equiv(exp):
      if not "|-" in exp or not "equiv" in exp:
        return
      return Binary( Context   , EquivTyp , SimpleCons(equiv))(exp) 
def Typing(exp):
     if not "|-" in exp:
      return
     return Binary( Context   , GenTyp , SimpleCons(typing))(exp)

def HottExp(exp):
 return Or( [Context, Typing, Equiv])(Tokenize(exp))
 
 
 
 

def IsBinOp(ast,op):
 if ast.name=="Constructor":
  if ast.operator.value =="app":
     if ast.left.name =="Constructor":
        if ast.left.operator.value =="app":
          if ast.left.left.name =="Leaf":
              if ast.left.left.value == op:
                return True
                
def IsUnOp(ast):
 if ast.name=="Constructor":
  if ast.operator.value =="app":
     if ast.left.name =="Leaf":
         if ast.left.value =="inv":
             return True
             
              
def ICompL(ast):
 return ast.left.right
 
def ICompR(ast):
 return ast.right

def IComp(ast):
 return ast.right 

 

def MakeIOp(op, left,right):
 opp = StringToTerm(op)
 return MakeApp2(opp, left, right) 
 
 
def MakeNOp(op,list):
 if len(list) == 0:
     return list
     
 if len(list) ==1:
     return list[0]
         
 if len(list) == 2:
    return MakeApp2(StringToTerm(op),list[0],list[1])
 return MakeApp2(StringToTerm(op), MakeNOp(op,list[1:]),list[0])
     

     

def MakeInv(ast):
 inv = StringToTerm("inv")
 return MakeApp(inv,ast)    
 
def ISym(ast):
 if IsBinOp(ast,"wedge") or IsBinOp(ast,"vee"):
    a = ICompL(aux)
    b = ICompR(aux)
    op = ast.operator.value
    return MakeIOp(op, b,a)
           
  


def Disp(ast,simple):
  if ast.name == "Leaf":
      return ast.value
  
#  if ast.operator.value =="subpoly":
#     aux = [ Disp2(x,simple)  for x in ast.children]
#     return "subpoly" + " " + " ".join(aux)      
      
  if ast.operator.value =="app":
      if simple== True:
       return  Disp(ast.left,simple) + " " + Disp(ast.right,simple)
      else:
       return  "("+Disp(ast.left,simple) + " " + Disp(ast.right,simple)+")"    
  if ast.operator.value =="lambda":
      return ast.operator.value +  " " + ast.operator.variable.value + "." + Disp(ast.children[0],simple)
  if ast.operator.value==":":
        return  Disp(ast.left,simple) + ":" + Disp(ast.right,simple)  
  if ast.operator.value=="|-":
            return  Disp(ast.left,simple) + "|-" + Disp(ast.right,simple)
  if ast.type=="Context":
     if len(ast.children)==0:
      return "" 
     aux = ""
     for i in range(0,len(ast.children)-1):
        aux = aux + Disp(ast.children[i],simple) + ","
     aux = aux + Disp(ast.children[len(ast.children)-1],simple)
     return aux
      
  if ast.type=="EquivTerm":
      return   Disp(ast.left,simple) + " equiv " + Disp(ast.right,simple)
      
  if ast.type=="EquivTyp":
      return   Disp(ast.left,simple) + ":" + Disp(ast.right,simple)
       
  if ast.type=="Equiv":
      return   Disp(ast.left,simple) + "|-" + Disp(ast.right,simple)
 
 
 
def IsApp4(t):
 if t.name!="Leaf":
   if t.operator.value=="app":
      if t.left.name!="Leaf":
         if t.left.operator.value=="app":
          if t.left.left.name!="Leaf":
              if t.left.left.operator.value =="app":
                 if t.left.left.left.name!="Leaf":
                       if t.left.left.left.operator.value =="app":
                           return True      
 
 
 
 
def Disp2(ast,simple):
   if ast.name == "Leaf":
       return ast.value
   
   if IsApp4(ast):
       
    if ast.left.left.left.left.name =="Leaf":
         if ast.left.left.left.left.value =="subpoly":
          d = ast.right
          c = ast.left.right
          b = ast.left.left.right
          a = ast.left.left.left.right  
    #  aux = [ Disp2(x,simple) for x in ast.children]
          return "[" + Disp2(a,simple) + Disp2(b,simple) + "," + Disp2(c,simple) + Disp2(d,simple) + "]"
         if ast.left.left.left.left.value =="comp":
               d = ast.right
               c = ast.left.right.children[0]
               b = ast.left.left.right
               a = ast.left.left.left.right.children[0]
               i = ast.left.left.left.right.operator.variable.value  
         #  aux = [ Disp2(x,simple) for x in ast.children]
         
               return "comp " + i + " "+  Disp2(a,simple) + "[" + Disp2(b,simple) + " -> " + Disp2(c,simple) + "]" + Disp2(d,simple)
         
       
       
       
          
   
   if ast.operator.value =="app":
     if ast.left.name =="Leaf":
       if ast.left.value=="inv":
         return "1-" + Disp2(ast.right,simple)       
     if ast.left.name=="Constructor" : 
       if ast.left.operator.value =="app":
         if ast.left.left.name =="Leaf":
           
           if ast.left.left.value in ["wedge", "vee", "equals"]:
              if ast.left.left.value =="wedge":
                return "(" + Disp2(ast.left.right,simple) +" ∧ " + Disp2(ast.right,simple) + ")"
              if ast.left.left.value =="vee":
                return "(" + Disp2(ast.left.right,simple) +" ∨ " + Disp2(ast.right,simple) + ")"
              if ast.left.left.value =="equals":
                return "(" + Disp2(ast.left.right,simple) +" = " + Disp2(ast.right,simple) + ")"
                      
                
           if ast.left.left.value in ["Pi", "Sigma"] and ast.right.name=="Constructor":
            if ast.right.operator.value=="lambda":   
             var = ast.right.operator.variable.value
             b = ast.right.children[0]
             a = ast.left.right
             if ast.left.left.value =="Pi":
                 
              return "(" + var + ":" + Disp2(a,simple) + ") -> " + Disp2(b,simple) 
             else:
              return "(" + var + ":" + Disp2(a,simple) + ") ⨉ " + Disp2(b,simple)          
           if ast.left.left.value =="Lambda" and ast.right.name=="Constructor": 
            if ast.right.operator.value=="lambda":      
             var = ast.right.operator.variable.value
             b = ast.right.children[0]
             a = ast.left.right
             return "λ(" + var + ":" + Disp2(a,simple) + ")" + Disp2(b,simple)
       
     if simple== True:
        return  Disp2(ast.left,simple) + " " + Disp2(ast.right,simple)
     else:
        return  "("+Disp2(ast.left,simple) + " " + Disp2(ast.right,simple)+")"    
   if ast.operator.value =="lambda":
    if ast.children[0].name =="Constructor":
      if ast.children[0].operator.value=="lambda":    
       l =   Disp2(ast.children[0],simple)     
       return "(λ"  + ast.operator.variable.value + "" + l[2:len(l)-1]    +")"
    return  "(λ"  + ast.operator.variable.value + "." +  Disp2(ast.children[0],simple)     +")"  
   if ast.operator.value==":":
       
       if Disp2(ast.left,simple) !="*":
         return  Disp2(ast.left,simple) + " : " + Disp2(ast.right,simple) 
       else:
           return  Disp2(ast.right,simple)  
          
   if ast.operator.value=="|-":
             return  Disp2(ast.left,simple) + "" + Disp2(ast.right,simple)
   if ast.type=="Context":
      if len(ast.children)==0:
       return " ⊢ " 
      aux = ""
      for i in range(0,len(ast.children)-1):
         aux = aux + Disp2(ast.children[i],simple) + ", "
      aux = aux + Disp2(ast.children[len(ast.children)-1],simple)
      return aux + " ⊢ "
      
   if ast.type=="EquivTerm":
       return   Disp2(ast.left,simple) + " ≡ " + Disp2(ast.right,simple)
      
   if ast.type=="EquivTyp":
       return   Disp2(ast.left,simple) + " : " + Disp2(ast.right,simple)
       
   if ast.type=="Equiv":
       return   Disp2(ast.left,simple) + " ⊢ " + Disp2(ast.right,simple)
               
       
def GetContextVariables(ast):
 aux = []
 for t in ast.children:
   aux.append(t.left.value)          
 return aux               

def GetTypingGenTyp(ast):
  return ast.right                
                
def GetTypingType(ast):
 return ast.right.right

def GetTypingTerm(ast):
 return ast.right.left
 
def GetTypingContext(ast):
 return ast.left 
 
def GetEquivType(ast):
    return ast.right.right

def GetEquivLeftTerm(ast):
    return ast.right.left.left

def GetEquivRightTerm(ast):
    return ast.right.left.right
    
def GetEquivContext(ast):
    return ast.left

def MakeVarTyp(left,type):
  op = Leaf(":", "VarTyp")
  aux = Constructor(op, "VarTyp", [left,type])
  return aux

def MakeGenTyp(left,type):
    op = Leaf(":", "GenTyp")
    aux = Constructor(op, "GenTyp", [left,type])
    return aux
    
def MakeTyping(context,gentyp):
    op = Leaf("|-", "Typing")
    aux = Constructor(op, "Typing", [context,gentyp])
    return aux
    
def StringToTerm(string):
    return HottTerm3(Tokenize(string))    
                
                
def MakeEquiv(context,left,right,type):
    op1 = Leaf("equiv", "EquivTerm")
    aux1 = Constructor(op1,"EquivTerm", [left,right])
    op2 = Leaf(":", "EquivTyp")
    aux2 = Constructor(op2,"EquivTyp", [aux1,type])
    op3 = Leaf("|-", "Equiv")
    aux3 = Constructor(op3, "Equiv",[context, aux2] )
    return aux3                
                
def MakeApp(left,right):
    op = Leaf("app", "HottTerm")
    aux = Constructor(op, "HottTerm", [left,right])
    
    return aux

def MakeApp2(left, a, b):
    return MakeApp(MakeApp(left,a),b)
    
def IsApp3(t):
 if t.name!="Leaf":
   if t.operator.value=="app":
      if t.left.name!="Leaf":
         if t.left.operator.value=="app":
          if t.left.left.name!="Leaf":
              if t.left.left.operator.value =="app":
                 return True                

def MakeApp3(left,a,b,c):
    return MakeApp(MakeApp2(left,a,b), c)

def MakeApp4(left,a,b,c,d):
    return MakeApp(MakeApp(MakeApp(MakeApp(left,a) ,b) , c) , d)
    
def MakeApp5(left,a,b,c,d,e):
    return MakeApp(MakeApp4(left,a,b,c,d), e)
            

def MakeApp6(left,a,b,c,d,e,f):
    return MakeApp2(MakeApp4(left,a,b,c,d), e,f)    
 
def MakeContext(children):
   op = Leaf("ctx","Context")
   aux = Constructor(op,"Context", children)
   return aux
    
def JoinContext(ctx1,ctx2):
    children = ctx1.children + ctx2.children
    op = Leaf("ctx","Context")
    aux = Constructor(op,"Context", children)
    return aux
        
        
def MakeLambda(var,term):
    
    op = Leaf("lambda", "HottTerm")
    op.variable = var
    aux = Constructor(op,"HottTerm", [term])
    return aux   
    

def MakeLambda2(var1,var2,term):
     aux = MakeLambda(var2,term)
     return MakeLambda(var1, aux)
     
def MakeLambda3(var1,var2,var3,term):
    aux = MakeLambda2(var2,var3,term)
    return MakeLambda(var1,aux)

def MakeDepLambda(x,A,B):
    #Check if x is in A
    return MakeApp2(Leaf("Lambda","HottTerm"), A, MakeLambda(x,B))
                     
#MakeContext      
                
def IsUniverse(ast):
     
 return ast.value[0]=="U" and ast.value[1:].isnumeric()
 

def IsTyping(ast):
 return ast.type == "Typing"

def IsDep(ast,kind):
 if ast.name=="Constructor":
   if ast.operator.value =="app":
     if ast.left.name=="Constructor":
        if ast.left.operator.value=="app" and ast.left.left.name=="Leaf":
          if ast.left.left.value==kind:
             if ast.right.name=="Constructor":
               if ast.right.operator.value=="lambda":
                 return True
 return False                                        
 
def GetDepTypA(ast,kind):
  if ast.name=="Constructor":
    if ast.operator.value =="app":
      if ast.left.name=="Constructor":
         if ast.left.operator.value=="app" and ast.left.left.name=="Leaf":
           if ast.left.left.value==kind:   
             return ast.left.right
             
             
def GetDepTypB(ast,kind):
  if ast.name=="Constructor":
    if ast.operator.value =="app":
      if ast.left.name=="Constructor":
         if ast.left.operator.value=="app" and ast.left.left.name=="Leaf":
           if ast.left.left.value==kind:   
             if ast.right.name=="Constructor":
               if ast.right.operator.value=="lambda":
                  return ast.right.children[0]
              
def GetDepTypx(ast,kind):
    if ast.name=="Constructor":
      if ast.operator.value =="app":
        if ast.left.name=="Constructor":
           if ast.left.operator.value=="app" and ast.left.left.name=="Leaf":
             if ast.left.left.value==kind:   
               if ast.right.name=="Constructor":
                 if ast.right.operator.value=="lambda":
                   return ast.right.operator.variable
   
 

        
def GetContextExtensionTyp(gamma):
    return   gamma.children[len(gamma.children)-1]       
                       

def GetContextExtensionTyp2(gamma):
    return   gamma.children[len(gamma.children)-2] 
          
def GetContextExtensionTyp3(gamma):
    return   gamma.children[len(gamma.children)-3]                             

def Cut1(gamma):
 if gamma.type=="Context":
  if len(gamma.children)>0:       
   aux = copy.deepcopy(gamma)
   children = aux.children[: len(aux.children)-1]
   aux.children = children
   return aux
 
def Cut2(gamma):
    return Cut1(Cut1(gamma)) 

def Cut3(gamma):
    return Cut1(Cut2(gamma))
 
def IsPlus(term):
 if term.name=="Constructor":
   if term.operator.value=="app" and term.children[0].name=="Constructor":
      if term.children[0].operator.value =="app" and term.children[0].children[0].value =="plus":
          return True
          
def GetPlusA(term):
  return term.left.right
 
def GetPlusB(term):
  return term.right
  
    
                           
 
     
                       
    
    
    