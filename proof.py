import copy
import pickle
from tokenizer import * 
import parser
from parser import *
from astop import *

class ProofElement:
  def __init__(self,name,dependencies,parameters,formula):
        self.name = name
        self.dependencies = dependencies
        self.parameters = parameters
        self.formula = formula
        self.pos = 0
        self.qed=False 
        self.comment=""

class ProofEnvironment:
 def __init__(self,proof,name):
       self.proof = proof
       self.name = name
       self.definitions = {}
       self.theorems = []
       self.log = []

 def ShowProof(self):
  n = 0     
  for  p in self.proof:
   print(str(n)+". "+ Disp2(p.formula, True) +"  "+p.name +" "+ ' '.join([str(y) for y in p.dependencies]))      
   n = n + 1
   
     
 def CtxEmp(self):
     aux = HottExp(".")
     proofelement = ProofElement("CtxEmp",[],[], aux)
     proofelement.pos = len(self.proof) + 1
     self.proof.append(proofelement)
     self.log.append("CtxEmp()")
     return True  

 def CtxExt(self,up,varstring):
     aux = self.proof[up].formula
     if aux.type=="Typing":
       vars = GetContextVariables(aux.left) 
       if not varstring in vars: 
         if varstring in constants:
             return   
         if not varstring in variables:
           variables.append(varstring)
         if IsUniverse(GetTypingType(aux)):
           newvar = StringToTerm(varstring)     
           t = GetTypingTerm(aux)
           oldcont = GetTypingContext(aux)
           newvartyp = MakeVarTyp(newvar,t)
           aux = copy.deepcopy(oldcont)
           aux.children.append(newvartyp)
           proofelement = ProofElement("CtxExt",[up],[varstring], aux)
           proofelement.pos = len(self.proof) + 1
           self.proof.append(proofelement)
           self.log.append("CtxExt(" + str(up) + "," + '"' + varstring + '"' + ")")
           return True      

 
               
 def Vble(self,up,n):
    aux = self.proof[up].formula
    if aux.type=="Context":
      t = copy.deepcopy(aux.children[n])
      t.type = "GenTyp"
      t.operator.type ="GenTyp"
      exp = MakeTyping(aux,t)
      proofelement = ProofElement("Vble",[up],[n], exp)
      proofelement.pos = len(self.proof) + 1
      self.proof.append(proofelement)
      self.log.append("Vble(" + str(up) + "," + str(n) + ")")
      return True      
                
 
 def Refl(self,up):
    aux = Proof.proof[up].formula
    if aux.type =="Typing":
     gamma = copy.deepcopy(GetTypingContext(aux))
     typ = copy.deepcopy(GetTypingType(aux))
     t = copy.deepcopy(GetTypingTerm(aux))
     exp = MakeEquiv(gamma, t,copy.deepcopy(t),typ)
     proofelement = ProofElement("Refl",[up],[], exp)
     proofelement.pos = len(self.proof) + 1
     self.proof.append(proofelement)
     self.log.append("Refl(" + str(up) +  ")")
     return True             
                
 def Sym(self,up):
  aux = self.proof[up].formula
  if aux.type=="Equiv":
    gamma = GetEquivContext(aux)
    left = GetEquivLeftTerm(aux)
    right = GetEquivRightTerm(aux)
    typ = GetEquivType(aux)
    exp = MakeEquiv(gamma, right,left, typ)
    proofelement = ProofElement("Sym",[up],[], exp)
    proofelement.pos = len(self.proof) + 1
    self.proof.append(proofelement)
    self.log.append("Sym(" + str(up) + ")")
    return True  

 def Trans(self,left,right):
   aux1 = self.proof[left].formula
   aux2 = self.proof[right].formula                   
   if aux1.type=="Equiv" and aux2.type=="Equiv":
     gamma1 = GetEquivContext(aux1)
     gamma2 = GetEquivContext(aux2)
     biga1 = GetEquivType(aux1)
     biga2 = GetEquivType(aux2)
     left1 = GetEquivLeftTerm(aux1)
     right1 = GetEquivRightTerm(aux1)
     left2 = GetEquivLeftTerm(aux2)
     right2 = GetEquivRightTerm(aux2)
     if Equals(gamma1,gamma2) and Equals(biga1,biga2):
       exp = MakeEquiv(gamma1, left1,right2, biga2)
       proofelement = ProofElement("Trans",[left,right],[], exp)
       proofelement.pos = len(self.proof) + 1
       self.proof.append(proofelement)
       self.log.append("Trans(" + str(left) + "," + str(right) + ")")
       return True    
   
   
 def Equiv1(left,right):
   aux1 = self.proof[left].formula
   aux2 = self.proof[right].formula                   
   if aux1.type=="Typing" and aux2.type=="Equiv":
     gamma1 = GetEquivContext(aux1)
     gamma2 = GetEquivContext(aux2)
     biga1 = GetTypingType(aux1)
     biga2 = GetEquivType(aux2)
     left = GetTypingTerm(aux1)
     left2 = GetEquivLeftTerm(aux2)
     right2 = GetEquivRightTerm(aux2)
     if Equals(gamma1,gamma2) and Equals(biga1,left2) and IsUniverse(biga2):
       exp = MakeTyping(gamma1, MakeGenTyp(left,right2))
       proofelement = ProofElement("Equiv1",[left,right],[], exp)
       proofelement.pos = len(self.proof) + 1
       self.proof.append(proofelement)
       self.log.append("Equiv1(" + str(left) + "," + str(right) + ")")
       return True     
        
     
 def Equiv2(self,left,right):
   aux1 = self.proof[left].formula
   aux2 = self.proof[right].formula                   
   if aux1.type=="Equiv" and aux2.type=="Equiv":
     gamma1 = GetEquivContext(aux1)
     gamma2 = GetEquivContext(aux2)
     biga1 = GetEquivType(aux1)
     biga2 = GetEquivType(aux2)
     left1 = GetEquivLeftTerm(aux1)
     right1 = GetEquivRightTerm(aux1)
     left2 = GetEquivLeftTerm(aux2)
     right2 = GetEquivRightTerm(aux2)
     if Equals(gamma1,gamma2) and Equals(biga1,left2) and IsUniverse(biga2):
       exp = MakeEquiv(gamma1, left1,right2, right2)
       proofelement = ProofElement("Equiv2",[left,right],[], exp)
       proofelement.pos = len(self.proof) + 1
       self.proof.append(proofelement)
       self.log.append("Equiv1(" + str(left) + "," + str(right) + ")")
       return True     
     
                                
                
 def UIntro(self, up,i):
   u1 = Leaf("U" + str(i),"HottTerm")
   u2 = Leaf("U" + str(i+1),"HottTerm")
   aux = Proof.proof[up].formula
   if aux.type=="Context":
    exp = MakeTyping(aux, MakeGenTyp(u1,u2))
    proofelement = ProofElement("UIntro",[up],[i], exp)
    proofelement.pos = len(self.proof) + 1
    self.proof.append(proofelement)
    self.log.append("UIntro(" + str(up) + "," + str(i) + ")")
    return True      
                            
 def UCumul(self,up):
    aux = Proof.proof[up].formula
    gamma = GetTypingContext(aux)
    biga = GetTypingTerm(aux)
    if aux.type=="Typing":
     u = GetTypingType(aux)
     if IsUniverse(u):
       i = int(u.value[1:])
       u2 = Leaf("U" + str(i+1),"HottTerm")
       exp = MakeTyping(gamma, MakeGenTyp(biga,u2))
       proofelement = ProofElement("UCumul",[up],[], exp)
       proofelement.pos = len(self.proof) + 1
       self.proof.append(proofelement)
       self.log.append("UCumul(" + str(up) + ")")
       return True
                     
                      
 def DepForm(self, left,right,dep):
  auxleft = Proof.proof[left].formula
  auxright = Proof.proof[right].formula
  if auxleft.type == "Typing" and auxright.type =="Typing":
    gamma = GetTypingContext(auxleft)
    gamma2 = GetTypingContext(auxright)
    if not IsContextExtension(gamma,gamma2):
     return
    vartyp = GetContextExtensionTyp(gamma2)
    gen1 = GetTypingGenTyp(auxleft)
    gen2 = GetTypingGenTyp(auxright)
    u1 = gen1.right
    u2 = gen2.right
    if IsUniverse(u1) and IsUniverse(u2) and Equals(u1,u2):
         a = gen1.left
         b = gen2.left
         lam = MakeLambda(vartyp.left, b)
         aux = MakeApp2(Leaf(dep, "HottTerm"), a, lam)
         t2 = MakeGenTyp(aux,u1)
         exp = MakeTyping(gamma, t2)
         proofelement = ProofElement(dep +"Form",[left,right],[], exp)
         proofelement.pos = len(self.proof) + 1
         self.proof.append(proofelement)
         self.log.append( dep + "Form(" + str(left) + "," + str(right) + ")")
         return True 
          
          
 def  PiIntro(self,up):
   aux = Proof.proof[up].formula
   if aux.type =="Typing":
     gamma = GetTypingContext(aux)
     if len(gamma.children)==0:
        return
     gamma2 = copy.deepcopy(gamma)
     gamma2.children = gamma2.children[0: len(gamma2.children)-1]
     vartyp = gamma.children[len(gamma.children)-1]
     bigb = GetTypingType(aux)
     b = GetTypingTerm(aux)
     x = vartyp.left
     biga = vartyp.right
     lam = MakeLambda(x, b)
     Lam = MakeApp2(Leaf("Lambda","HottTerm"), biga, lam)
     lam2 = MakeLambda(x,bigb)
     Pi = MakeApp2(Leaf("Pi", "HottTerm"), biga, lam2)   
     gentyp = MakeGenTyp(Lam,Pi)
     exp = MakeTyping(gamma2, gentyp)
     proofelement = ProofElement("PiIntro",[up],[], exp)
     proofelement.pos = len(self.proof) + 1
     self.proof.append(proofelement)
     self.log.append("PiIntro(" + str(up) +  ")")
     return True             

 def PiElim(self,lef,righ):
  left =  Proof.proof[lef].formula
  right = Proof.proof[righ].formula 
  if Equals(GetTypingContext(left), GetTypingContext(right)):
    pi = GetTypingType(left)
    if IsDep(pi,"Pi"): 
     f = GetTypingTerm(left)
     a = GetTypingTerm(right)
     biga = GetTypingType(right)
     bigb = GetDepTypB(pi,"Pi")
     gamma = GetTypingContext(left)
     x = GetDepTypx(pi,"Pi")
     if Equals(GetDepTypA(pi,"Pi"), biga):
         newbigb = Substitution(bigb, x, a)
         aux = MakeApp(f,a)
         exp = MakeTyping(gamma,MakeGenTyp(aux,newbigb))
         proofelement = ProofElement("PiElim",[lef,righ],[], exp)
         proofelement.pos = len(self.proof) + 1
         self.proof.append(proofelement)
         self.log.append("PiElim(" + str(lef) + "," + str(righ) +  ")")
         return True
         
 def PiComp(self,left,right):
     gamma1 = copy.deepcopy(GetTypingContext(Proof.proof[left].formula))
     gamma = GetTypingContext(Proof.proof[right].formula)
     if len(gamma1.children) == len(gamma.children) + 1:
       vartyp = gamma1.children[len(gamma1.children) -1]
       gamma1.children = gamma1.children[:len(gamma1.children)-1]
       if Equals(gamma1,gamma): 
          biga1 = vartyp.right
          x = vartyp.left
          biga2 = GetTypingType(Proof.proof[right].formula)
          if Equals(biga1,biga2):
            bigb =  GetTypingType(Proof.proof[left].formula)          
            b = GetTypingTerm(Proof.proof[left].formula)  
            a = GetTypingTerm(Proof.proof[right].formula)
            exp = MakeEquiv(gamma, MakeApp(MakeDepLambda(x,biga1,b), a), Substitution(b,x,a), Substitution(bigb,x,a) ) 
            proofelement = ProofElement("PiComp",[left,right],[], exp)
            proofelement.pos = len(self.proof) + 1
            self.proof.append(proofelement)
            self.log.append("PiComp(" + str(left) + "," + str(right) +  ")")
            return True


 def PiUniq(self,up):
  aux = Proof.proof[up].formula
  if  IsDep(GetTypingType(aux),"Pi"):
    gamma = GetTypingContext(aux)
    f = GetTypingTerm(aux)
    pi = GetTypingType(aux)
    biga = GetDepTypA(pi,"Pi")
    bigb = GetDepTypB(pi,"Pi")
    x = GetDepTypx(pi,"Pi")
    aux2 =  MakeDepLambda(x,biga,MakeApp(f,x))
    exp = MakeEquiv(gamma, f, aux2, pi)
    proofelement = ProofElement("PiUniq",[up],[], exp)
    proofelement.pos = len(self.proof) + 1
    self.proof.append(proofelement)
    self.log.append("PiUniq(" + str(up) +  ")")
    return True
          
 def SigmaIntro(self, up, left, right):
   aux1 = copy.deepcopy(Proof.proof[up].formula)
   aux2 = Proof.proof[left].formula
   aux3 = copy.deepcopy(Proof.proof[right].formula)
   u = GetTypingType(aux1)
   if IsUniverse(u):
     gamma1 = GetTypingContext(aux1)
     gamma2 = GetTypingContext(aux2)
     gamma3 = GetTypingContext(aux3)   
     if Equals(gamma2,gamma3) and IsContextExtension(gamma2,gamma1):
        t = GetContextExtensionTyp(gamma1)
        bigb = GetTypingTerm(aux1)
        a = GetTypingTerm(aux2)
        biga = GetTypingType(aux2)
        b = GetTypingTerm(aux3)
        prebigb = GetTypingType(aux3)
        if Equals(t.right,biga) and Equals(prebigb, Substitution(bigb, t.left, a)):
            term = MakeApp2(Leaf("pair","HottTerm"), a, b)
            typ = MakeApp2(Leaf("Sigma", "HottTerm"), biga, MakeLambda(t.left, bigb))
            exp = MakeTyping(gamma2, MakeGenTyp(term,typ))
            proofelement = ProofElement("SigmaIntro",[up,left,right],[], exp)
            proofelement.pos = len(self.proof) + 1
            self.proof.append(proofelement)
            self.log.append("SigmaIntro(" + str(up) + "," + str(left) +"," + str(right) + ")")
            return True
        
     
 def SigmaElim(self,up,left,right):     
  aux1 = Proof.proof[up].formula
  aux2 = Proof.proof[left].formula
  aux3 = Proof.proof[right].formula         
  if IsTyping(aux1) and IsTyping(aux2) and IsTyping(aux3):
   p = GetTypingTerm(aux3)
   t3 = GetTypingType(aux3) 
   if IsDep(t3,"Sigma"):
       
    g = GetTypingTerm(aux2)
    prec = GetTypingType(aux2)
    gamma2 = GetTypingContext(aux2)
    gamma3 = GetTypingContext(aux3)
    if len(gamma2.children)> 1:
      gamma2cut = copy.deepcopy(gamma2)
      gamma2cut.children = gamma2cut.children[:len(gamma2.children)-2]
      typ1 = gamma2.children[len(gamma2.children)-2]
      typ2 = gamma2.children[len(gamma2.children)-1]
      x = typ1.left
      biga = typ1.right
      bigb = typ2.right
      sigtyp2 = MakeApp2(Leaf("Sigma", "HottTerm"), biga, MakeLambda(x, bigb))
      
      gamma1 = GetTypingContext(aux1)
      
      if IsContextExtension(gamma3,gamma1) and Equals(gamma2cut, gamma3):
              
          zee = gamma1.children[len(gamma1.children)-1]
          if Equals(zee.right, t3) and Equals(t3,sigtyp2):
              z = zee.left
              bigc = GetTypingTerm(aux1)
              if IsUniverse(GetTypingType(aux1)):
                y = typ2.left
                pair = MakeApp2(Leaf("pair","HottTerm"), x, y)
                if Equals(prec, Substitution(bigc, z, pair ) ):
                    newc = Substitution(bigc, z,p)
                    aux1 = MakeApp4(Leaf("ind","HottTerm"), sigtyp2, MakeLambda(z,bigc), MakeLambda2(x,y,g),p )
                    exp = MakeTyping(gamma3, MakeGenTyp(aux1,newc))
                    proofelement = ProofElement("SigmaElim",[up,left,right],[], exp)
                    proofelement.pos = len(self.proof) + 1
                    self.proof.append(proofelement)
                    self.log.append("SigmaElim(" + str(up) + "," + str(left) +"," + str(right) + ")")
                    return True
                    
                    
                     
                  
 def SigmaComp(self,up, left,right1,right2):
    aux1 = Proof.proof[up].formula
    aux2 = Proof.proof[left].formula
    aux3 = Proof.proof[right1].formula
    aux4 = Proof.proof[right2].formula
    a =  GetTypingTerm(aux3)
    b = GetTypingTerm(aux4)
    g = GetTypingTerm(aux2)
    if IsTyping(aux1) and IsTyping(aux2) and IsTyping(aux3) and IsTyping(aux4):
     gamma1 = GetTypingContext(aux1)
     gamma2 = GetTypingContext(aux2)
     gamma3 = GetTypingContext(aux3)
     gamma4 = GetTypingContext(aux4)
     if Equals(gamma3,gamma4) and IsContextExtension(gamma3,gamma1):     
      gamma2cut = copy.deepcopy(gamma2)
      gamma2cut.children = gamma2cut.children[:len(gamma2.children)-2]
      gamma1cut = copy.deepcopy(gamma1)
      gamma1cut.children = gamma1cut.children[:len(gamma1.children)-1]
      typ1 = gamma2.children[len(gamma2.children)-2]
      typ2 = gamma2.children[len(gamma2.children)-1]
      x = typ1.left
      y = typ2.left
      biga = typ1.right
      bigb = typ2.right
      sigtyp2 = MakeApp2(Leaf("Sigma", "HottTerm"), biga, MakeLambda(x, bigb))
      zee = gamma1.children[len(gamma1.children)-1]
      z = zee.left
      bigc = GetTypingTerm(aux1)
      bigc2 = GetTypingType(aux2)
      u = GetTypingType(aux1)
      pair = MakeApp2(Leaf("pair","HottTerm"), x, y)
      if Equals(sigtyp2, zee.right)   and IsUniverse(u) and Equals(bigc2, Substitution(bigc, z, pair )):
          
       
       if Equals(gamma2cut,gamma1cut) and Equals(gamma1cut,gamma3):
          
        if Equals(GetTypingType(aux3), biga) and Equals(GetTypingType(aux4), Substitution(bigb,x,a)):
          pair2 =  MakeApp2(Leaf("pair","HottTerm"), a, b)
          aux1 = MakeApp4(Leaf("ind","HottTerm"), sigtyp2, MakeLambda(z,bigc), MakeLambda2(x,y,g),pair2 )
          newg = PairSubstitution(g,[x,y],[a,b])
          exp = MakeEquiv(gamma3, aux1, newg, Substitution(bigc, z, pair2))
          proofelement = ProofElement("SigmaComp",[up,left,right1,right2],[], exp)
          proofelement.pos = len(self.proof) + 1
          self.proof.append(proofelement)
          self.log.append("SigmaComp(" + str(up) + "," + str(left) +"," + str(right1) +"," + str(right2) + ")")
          return True
                                            
 
 def PlusForm(self,left,right):
   aux1 = Proof.proof[left].formula
   aux2 = Proof.proof[right].formula
   if aux1.type =="Typing" and aux2.type =="Typing":
       u1 = GetTypingType(aux1)
       u2 = GetTypingType(aux2)
       if IsUniverse(u1) and IsUniverse(u2) and Equals(u1,u2):
        gamma1 = GetTypingContext(aux1)
        gamma2 = GetTypingContext(aux2)
        biga = GetTypingTerm(aux1)
        bigb = GetTypingTerm(aux2)
        if Equals(gamma1,gamma2):
         aux = MakeApp2(Leaf("plus", "HottTerm"), biga, bigb )
         exp = MakeTyping(gamma1, MakeGenTyp(aux,u1))
         proofelement = ProofElement("PlusForm",[left,right],[], exp)
         proofelement.pos = len(self.proof) + 1
         self.proof.append(proofelement)
         self.log.append("PlusForm(" + str(left) + "," + str(right) + ")")
         return True                   
     
 def PlusIntro(self,left,right,up,side):
    aux1 = Proof.proof[left].formula
    aux2 = Proof.proof[right].formula
    aux3 = Proof.proof[up].formula
    if aux1.type =="Typing" and aux2.type =="Typing" and aux3.type =="Typing":
        u1 = GetTypingType(aux1)
        u2 = GetTypingType(aux2)
        if IsUniverse(u1) and IsUniverse(u2) and Equals(u1,u2):
         gamma1 = GetTypingContext(aux1)
         gamma2 = GetTypingContext(aux2)
         gamma3 = GetTypingContext(aux3)
         biga = GetTypingTerm(aux1)
         bigb = GetTypingTerm(aux2)
         if Equals(gamma1,gamma2) and Equals(gamma1,gamma3):
           biga2 = GetTypingType(aux3)
           a = GetTypingTerm(aux3)
           if side ==1:
            if Equals(biga2,biga):
             aux = MakeApp(Leaf("inl","HottTerm"), a)
             plus = MakeApp2(Leaf("plus", "HottTerm"), biga, bigb)
             exp = MakeTyping(gamma1, MakeGenTyp(aux, plus))
             proofelement = ProofElement("PlusIntro",[left,right,up],[side], exp)
             proofelement.pos = len(self.proof) + 1
             self.proof.append(proofelement)
             self.log.append("PlusIntro(" + str(left) + "," + str(right) + "," + str(up) + ","+ str(side) + ")")
             return True  
           if side ==2:
            
             if Equals(biga2,bigb):
                aux = MakeApp(Leaf("inr","HottTerm"), a)
                plus = MakeApp2(Leaf("plus", "HottTerm"), biga, bigb)
                exp = MakeTyping(gamma1, MakeGenTyp(aux, plus))
                proofelement = ProofElement("PlusIntro",[left,right,up],[side], exp)
                proofelement.pos = len(self.proof) + 1
                self.proof.append(proofelement)
                self.log.append("PlusIntro(" + str(left) + "," + str(right) + "," + str(up) + ","+ str(side) + ")")
                return True  
                      
              
              
 def PlusElim(self, up,left,right,down):
   aux1 = Proof.proof[up].formula
   aux2 = Proof.proof[left].formula
   aux3 = Proof.proof[right].formula                
   aux4 = Proof.proof[down].formula
   if aux1.type=="Typing" and aux2.type=="Typing" and aux3.type=="Typing" and aux4.type=="Typing":
     
     gamma1 = GetTypingContext(aux1)
     gamma2 = GetTypingContext(aux2)
     gamma3 = GetTypingContext(aux3)
     gamma4 = GetTypingContext(aux4)
     gamma1cut = Cut1(gamma1)
     gamma2cut = Cut1(gamma2)
     gamma3cut = Cut1(gamma3)
     if Equals(gamma1cut,gamma2cut) and Equals(gamma2cut,gamma3cut) and Equals(gamma3cut,gamma4):
         
         ext1 = GetContextExtensionTyp(gamma1)
         ext2 = GetContextExtensionTyp(gamma2)
         ext3 = GetContextExtensionTyp(gamma3)
         e = GetTypingTerm(aux4)
         plus = GetTypingType(aux4)
         c = GetTypingTerm(aux2)
         d = GetTypingTerm(aux3)
         bigc = GetTypingTerm(aux1)
         u = GetTypingType(aux1)
         bigc1 = GetTypingType(aux2)
         bigc2 = GetTypingType(aux3)
         if IsPlus(plus) and Equals(ext1.right,plus) and IsUniverse(u):
           
           biga1 = ext2.right
           bigb1 = ext3.right
          
           
           if Equals(biga1, GetPlusA(plus)) and Equals(bigb1, GetPlusB(plus)):
               
               inl = MakeApp(Leaf("inl","HottTerm"), ext2.left)
               inr = MakeApp(Leaf("inr","HottTerm"), ext3.left)
               z = ext1.left
               if Equals(bigc1, Substitution(bigc,z,inl)) and Equals(bigc2, Substitution(bigc, z,inr)):
                  t = MakeApp5(Leaf("ind","HottTerm"),plus, MakeLambda(z,bigc), MakeLambda(ext2.left, c), MakeLambda(ext3.left, d),e )
                 
                  newbigc = Substitution(bigc, z, e)
                  exp = MakeTyping(gamma4, MakeGenTyp(t, newbigc ))
                  proofelement = ProofElement("PlusElim",[up,left,right,down],[], exp)
                  proofelement.pos = len(self.proof) + 1
                  self.proof.append(proofelement)
                  self.log.append("PlusElim(" + str(up) + "," + str(left) + "," + str(right) + ","+ str(down) + ")")
                  return True    
         
                                 
 def PlusComp(self, up,left,right,down,side):
   aux1 = Proof.proof[up].formula
   aux2 = Proof.proof[left].formula
   aux3 = Proof.proof[right].formula                
   aux4 = Proof.proof[down].formula
   if aux1.type=="Typing" and aux2.type=="Typing" and aux3.type=="Typing" and aux4.type=="Typing":
     
     gamma1 = GetTypingContext(aux1)
     gamma2 = GetTypingContext(aux2)
     gamma3 = GetTypingContext(aux3)
     gamma4 = GetTypingContext(aux4)
     gamma1cut = Cut1(gamma1)
     gamma2cut = Cut1(gamma2)
     gamma3cut = Cut1(gamma3)
     if Equals(gamma1cut,gamma2cut) and Equals(gamma2cut,gamma3cut) and Equals(gamma3cut,gamma4):
         
         ext1 = GetContextExtensionTyp(gamma1)
         ext2 = GetContextExtensionTyp(gamma2)
         ext3 = GetContextExtensionTyp(gamma3)
         a = GetTypingTerm(aux4)
         biga = GetTypingType(aux4)
         c = GetTypingTerm(aux2)
         d = GetTypingTerm(aux3)
         bigc = GetTypingTerm(aux1)
         u = GetTypingType(aux1)
         bigc1 = GetTypingType(aux2)
         bigc2 = GetTypingType(aux3)
         if IsPlus(ext1.right):
             
           biga2 = GetPlusA(ext1.right)
           bigb2 = GetPlusB(ext1.right)      
           biga1 = ext2.right
           bigb1 = ext3.right
           if Equals(biga1, biga2) and Equals(bigb1, bigb2):
              
               inl = MakeApp(Leaf("inl","HottTerm"), ext2.left)
               inr = MakeApp(Leaf("inr","HottTerm"), ext3.left)
               ina = MakeApp(Leaf("inl","HottTerm"), a)
               inb = MakeApp(Leaf("inr","HottTerm"), a)
               z = ext1.left
               if Equals(bigc1, Substitution(bigc,z,inl)) and Equals(bigc2, Substitution(bigc, z,inr)):
                if side ==1:
                 if Equals(biga, biga1):        
                  t = MakeApp5(Leaf("ind","HottTerm"),ext1.right, MakeLambda(z,bigc), MakeLambda(ext2.left, c), MakeLambda(ext3.left, d),ina )
                  newbigc = Substitution(bigc, z, ina)
                  newc = Substitution(c,ext2.left, a)
                  exp = MakeEquiv(gamma4, t, newc, newbigc)
                  proofelement = ProofElement("PlusComp",[up,left,right,down,side],[], exp)
                  proofelement.pos = len(self.proof) + 1
                  self.proof.append(proofelement)
                  self.log.append("PlusComp(" + str(up) + "," + str(left) + "," + str(right) + ","+ str(down) + "," + str(side) +")")
                  return True    
               if side ==2:
                if Equals(biga, bigb1):        
                 t = MakeApp5(Leaf("ind","HottTerm"),ext1.right, MakeLambda(z,bigc), MakeLambda(ext2.left, c), MakeLambda(ext3.left, d),inb )
                 newbigc = Substitution(bigc, z, inb)
                 newc = Substitution(d,ext2.left, a)
                 exp = MakeEquiv(gamma4, t, newc, newbigc)
                 proofelement = ProofElement("PlusComp",[up,left,right,down],[side], exp)
                 proofelement.pos = len(self.proof) + 1
                 self.proof.append(proofelement)
                 self.log.append("PlusComp(" + str(up) + "," + str(left) + "," + str(right) + ","+ str(down) + "," + str(side) +")")
                 return True    
             
 
 
 def OForm(self,up,i):
   aux = self.proof[up].formula
   if aux.type =="Context":
    un = "U"+str(i)
    global constants
    if not un in constants:
     constants.append(un)
     parser.constants.append(un)
    
    uni = StringToTerm(un)
    one = StringToTerm("O")
    typ = MakeGenTyp(one,uni)
    
    exp = MakeTyping(aux,typ)
    proofelement = ProofElement("OForm",[up],[i], exp)
    proofelement.pos = len(self.proof) + 1
    self.proof.append(proofelement)
    self.log.append("OForm(" + str(up) + "," + str(i) + ")")
    return True
               
 def OElim(self,left,right):
  aux1 = Proof.proof[left].formula
  aux2 = Proof.proof[right].formula
  if IsTyping(aux1) and  IsTyping(aux2): 
    gamma1 = GetTypingContext(aux1)
    gamma2 = GetTypingContext(aux2)
    if IsContextExtension(gamma2,gamma1):
     bigc = GetTypingTerm(aux1)
     u = GetTypingType(aux1)
     a = GetTypingTerm(aux2)
     o = Leaf("O", "HottTerm")
     g = GetContextExtensionTyp(gamma1)
     if Equals(g.right,o) and Equals(o, GetTypingType(aux2)) and IsUniverse(u):
        t = MakeApp3(Leaf("ind","HottTerm"), o, MakeLambda(g.left, bigc) ,a )
        exp = MakeTyping(gamma2, MakeGenTyp(t, Substitution(bigc, g.left, a)))
        proofelement = ProofElement("OElim",[left,right],[], exp)
        proofelement.pos = len(self.proof) + 1
        self.proof.append(proofelement)
        self.log.append("OElim(" + str(left) + "," + str(right) + ")")
        return True
         

 def NatForm(self,up,i):
   aux = self.proof[up].formula
   if aux.type =="Context":
    un = "U"+str(i)
    global constants
    if not un in constants:
     constants.append(un)
    if not un in parser.constants: 
     parser.constants.append(un)
    
    uni = StringToTerm(un)
    nat = StringToTerm("Nat")
    typ = MakeGenTyp(nat,uni)
    
    exp = MakeTyping(aux,typ)
    proofelement = ProofElement("NatForm",[up],[i], exp)
    proofelement.pos = len(self.proof) + 1
    self.proof.append(proofelement)
    self.log.append("NatForm(" + str(up) + "," + str(i) + ")")
    return True     
     
 def NatIntro1(self,up ):
   aux = self.proof[up].formula
   if aux.type =="Context":
   
    zero = StringToTerm("0")
    nat = StringToTerm("Nat")
    typ = MakeGenTyp(zero,nat)
    
    exp = MakeTyping(aux,typ)
    proofelement = ProofElement("NatIntro1",[up],[], exp)
    proofelement.pos = len(self.proof) + 1
    self.proof.append(proofelement)
    self.log.append("NatIntro1(" + str(up)  + ")")
    return True
  
 def NatIntro2(self,up):
    aux = self.proof[up].formula
    if IsTyping(aux):
      gamma = GetTypingContext(aux)
      n = GetTypingTerm(aux)
      nat = GetTypingType(aux)
      if Equals(nat, Leaf("Nat","HottTerm")):
         exp = MakeTyping( gamma , MakeGenTyp(MakeApp( Leaf("succ", "HottTerm") ,  n ) , nat) )
         proofelement = ProofElement("NatIntro2",[up],[], exp)
         proofelement.pos = len(self.proof) + 1
         self.proof.append(proofelement)
         self.log.append("NatIntro2(" + str(up)  + ")")
         return True       
 
 
 def NatElim(self, up,left,right,down):
  aux1 = Proof.proof[up].formula
  aux2 = Proof.proof[left].formula
  aux3 = Proof.proof[right].formula                
  aux4 = Proof.proof[down].formula
  if aux1.type=="Typing" and aux2.type=="Typing" and aux3.type=="Typing" and aux4.type=="Typing":
    
   gamma1 = GetTypingContext(aux1)
   gamma2 = GetTypingContext(aux2)
   gamma3 = GetTypingContext(aux3)
   gamma4 = GetTypingContext(aux4)
   if len(gamma1.children) > 0 and len(gamma3.children) > 1: 
    gamma1cut = Cut1(gamma1)
    gamma3cut = Cut2(gamma3)   
    if Equals(gamma1cut, gamma2) and Equals(gamma2, gamma3cut) and Equals(gamma3cut, gamma4):
      n = GetTypingTerm(aux4)
      nat = GetTypingType(aux4)
      trnat = StringToTerm("Nat")
      bigc = GetTypingTerm(aux1)
      u = GetTypingType(aux1)
      var = GetContextExtensionTyp(gamma1)
      x = var.left
      nat2 = var.right
      c0 = GetTypingTerm(aux2)
      bigc2 = GetTypingType(aux2)
      varx = GetContextExtensionTyp2(gamma3)
      vary = GetContextExtensionTyp(gamma3)
      bigc3 = GetTypingType(aux3)
      cs = GetTypingTerm(aux3)
      succ = MakeApp( Leaf("succ", "HottTerm") ,  x )
      
      if Equals(bigc, vary.right) and IsUniverse(u) and Equals(trnat,nat) and Equals(nat2,trnat):
        if Equals(trnat, varx.right) and Equals(bigc2, Substitution(bigc, x, Leaf("0","HottTerm"))):
            
            if Equals(vary.right, bigc) and Equals(x, varx.left):
             
              if Equals(bigc3, Substitution(bigc,x, succ)):
                  
                t = MakeApp5(Leaf("ind","HottTerm"), Leaf("Nat","HottTerm"), MakeLambda(x, bigc), c0, MakeLambda2(x,vary.left,cs), n   )
                exp = MakeTyping(gamma2, MakeGenTyp(t, Substitution(bigc,x, n)  ) )
                proofelement = ProofElement("NatElim",[up,left,right,down],[], exp)
                proofelement.pos = len(self.proof) + 1
                self.proof.append(proofelement)
                self.log.append("NatElim(" + str(up) + "," + str(left) + "," + str(right) + ","+ str(down) +")")
                return True    
                    
          
      
 def NatComp2(self, up,left,right,down):
  aux1 = Proof.proof[up].formula
  aux2 = Proof.proof[left].formula
  aux3 = Proof.proof[right].formula                
  aux4 = Proof.proof[down].formula
  if aux1.type=="Typing" and aux2.type=="Typing" and aux3.type=="Typing" and aux4.type=="Typing":
    
   gamma1 = GetTypingContext(aux1)
   gamma2 = GetTypingContext(aux2)
   gamma3 = GetTypingContext(aux3)
   gamma4 = GetTypingContext(aux4)
   if len(gamma1.children) > 0 and len(gamma3.children) > 1: 
    gamma1cut = Cut1(gamma1)
    gamma3cut = Cut2(gamma3)   
    if Equals(gamma1cut, gamma2) and Equals(gamma2, gamma3cut) and Equals(gamma3cut, gamma4):
      n = GetTypingTerm(aux4)
      nat = GetTypingType(aux4)
      trnat = StringToTerm("Nat")
      bigc = GetTypingTerm(aux1)
      u = GetTypingType(aux1)
      var = GetContextExtensionTyp(gamma1)
      x = var.left
      nat2 = var.right
      c0 = GetTypingTerm(aux2)
      bigc2 = GetTypingType(aux2)
      varx = GetContextExtensionTyp2(gamma3)
      vary = GetContextExtensionTyp(gamma3)
      bigc3 = GetTypingType(aux3)
      cs = GetTypingTerm(aux3)
      succ = MakeApp( Leaf("succ", "HottTerm") ,  x )
      succn = MakeApp( Leaf("succ", "HottTerm") ,  n )
      
      if Equals(bigc, vary.right) and IsUniverse(u) and Equals(trnat,nat) and Equals(nat2,trnat):
        if Equals(trnat, varx.right) and Equals(bigc2, Substitution(bigc, x, Leaf("0","HottTerm"))):
            
            if Equals(vary.right, bigc) and Equals(x, varx.left):
             
              if Equals(bigc3, Substitution(bigc,x, succ)):
                  
                t = MakeApp5(Leaf("ind","HottTerm"), Leaf("Nat","HottTerm"), MakeLambda(x, bigc), c0, MakeLambda2(x,vary.left,cs), succn  )
                tprev =  MakeApp5(Leaf("ind","HottTerm"), Leaf("Nat","HottTerm"), MakeLambda(x, bigc), c0, MakeLambda2(x,vary.left,cs), n  )
                cssub = PairSubstitution(cs, [x, vary.left], [n, tprev  ])
                newc = Substitution(bigc,x, succn)
                exp = MakeEquiv(gamma2, t, cssub, newc)
                
                
                proofelement = ProofElement("NatComp2",[up,left,right,down],[], exp)
                proofelement.pos = len(self.proof) + 1
                self.proof.append(proofelement)
                self.log.append("NatComp2(" + str(up) + "," + str(left) + "," + str(right) + ","+ str(down) +")")
                return True    
      
 
 def NatComp1(self, up,left,right):
  aux1 = Proof.proof[up].formula
  aux2 = Proof.proof[left].formula
  aux3 = Proof.proof[right].formula                
  
  if aux1.type=="Typing" and aux2.type=="Typing" and aux3.type=="Typing" :
    
   gamma1 = GetTypingContext(aux1)
   gamma2 = GetTypingContext(aux2)
   gamma3 = GetTypingContext(aux3)
  
   if len(gamma1.children) > 0 and len(gamma3.children) > 1: 
    gamma1cut = Cut1(gamma1)
    gamma3cut = Cut2(gamma3)   
    if Equals(gamma1cut, gamma2) and Equals(gamma2, gamma3cut) :
     
      trnat = StringToTerm("Nat")
      bigc = GetTypingTerm(aux1)
      u = GetTypingType(aux1)
      var = GetContextExtensionTyp(gamma1)
      x = var.left
      nat2 = var.right
      c0 = GetTypingTerm(aux2)
      bigc2 = GetTypingType(aux2)
      varx = GetContextExtensionTyp2(gamma3)
      vary = GetContextExtensionTyp(gamma3)
      bigc3 = GetTypingType(aux3)
      cs = GetTypingTerm(aux3)
      succ = MakeApp( Leaf("succ", "HottTerm") ,  x )
      
      
      if Equals(bigc, vary.right) and IsUniverse(u)  and Equals(nat2,trnat):
        if Equals(trnat, varx.right) and Equals(bigc2, Substitution(bigc, x, Leaf("0","HottTerm"))):
            
            if Equals(vary.right, bigc) and Equals(x, varx.left):
             
              if Equals(bigc3, Substitution(bigc,x, succ)):
                  
                t = MakeApp5(Leaf("ind","HottTerm"), Leaf("Nat","HottTerm"), MakeLambda(x, bigc), c0, MakeLambda2(x,vary.left,cs), Leaf("0","HottTerm")  )
               
               
                exp = MakeEquiv(gamma2, t, c0, bigc2)
                
                
                proofelement = ProofElement("NatComp2",[up,left,right],[], exp)
                proofelement.pos = len(self.proof) + 1
                self.proof.append(proofelement)
                self.log.append("NatComp2(" + str(up) + "," + str(left) + "," + str(right)  +")")
                return True    
        
      
 def EqForm(self,left,center,right):
   aux1 = Proof.proof[left].formula
   aux2 = Proof.proof[center].formula
   aux3 = Proof.proof[right].formula
   if aux1.type=="Typing" and aux2.type=="Typing" and aux3.type =="Typing":
     gamma1 = GetTypingContext(aux1)
     gamma2 = GetTypingContext(aux2)
     gamma3 = GetTypingContext(aux3)                
     if Equals(gamma1,gamma2) and Equals(gamma2,gamma3):
      u = GetTypingType(aux1)
      biga1 = GetTypingType(aux2)
      biga2 = GetTypingType(aux3)
      biga = GetTypingTerm(aux1)
      if IsUniverse(u) and Equals(biga1,biga2) and Equals(biga1,biga):
         a = GetTypingTerm(aux2)  
         b = GetTypingTerm(aux3)
         t = MakeApp3(Leaf("equals","HottTerm"), biga, a , b )
         exp = MakeTyping(gamma1, MakeGenTyp(t,u ))
         proofelement = ProofElement("EqForm",[left,center,right],[], exp)
         proofelement.pos = len(self.proof) + 1
         self.proof.append(proofelement)
         self.log.append("EqForm(" + str(left) + "," + str(center) + "," + str(right)  +")")
         return True    
         
 def EqIntro(self,left,right):
   aux1 = Proof.proof[left].formula
  
   aux2 = Proof.proof[right].formula
   if aux1.type=="Typing" and aux2.type=="Typing":
     gamma1 = GetTypingContext(aux1)
     gamma2 = GetTypingContext(aux2)
                 
     if Equals(gamma1,gamma2):
      u = GetTypingType(aux1)
      biga1 = GetTypingTerm(aux1)
      biga2 = GetTypingType(aux2)
      a = GetTypingTerm(aux2)
      if IsUniverse(u) and Equals(biga1,biga2):
         
         ref = MakeApp(Leaf("refl","HottTerm"),a)
         t = MakeApp3(Leaf("equals","HottTerm"), biga1, a , a )
         exp = MakeTyping(gamma1, MakeGenTyp(ref, t ))
         proofelement = ProofElement("EqIntro",[left,right],[], exp)
         proofelement.pos = len(self.proof) + 1
         self.proof.append(proofelement)
         self.log.append("EqIntro(" + str(left)  + "," + str(right)  +")")
         return True    
         
           
  
 def EqElim(self, ty1,ty2,ty3,ty4,ty5):
  aux1 = Proof.proof[ty1].formula
  aux2 = Proof.proof[ty2].formula
  aux3 = Proof.proof[ty3].formula
  aux4 = Proof.proof[ty4].formula
  aux5 = Proof.proof[ty5].formula
  if aux1.type=="Typing" and aux2.type=="Typing" and aux3.type=="Typing" and aux4.type=="Typing" and aux5.type=="Typing":
     
    gamma3 = GetTypingContext(aux3)
    gamma4 = GetTypingContext(aux4)
    gamma5 = GetTypingContext(aux5)
    a = GetTypingTerm(aux3)
    b = GetTypingTerm(aux4)
    biga1 = GetTypingType(aux3)
    biga2 = GetTypingType(aux4)
    eq = MakeApp3(Leaf("equals","HottTerm"), biga1, a , b )
    eq1 = GetTypingType(aux5)
    p1 = GetTypingTerm(aux5)
    if Equals(gamma3,gamma4) and Equals(gamma4,gamma5) and Equals(biga1,biga2) and Equals(eq,eq1):
     
     gamma1 = GetTypingContext(aux1)
     gamma2 = GetTypingContext(aux2)
     if len(gamma1.children)> 2 and len(gamma2.children)>0:
      
      gamma1cut = Cut3(gamma1)
      gamma2cut = Cut1(gamma2)
      if Equals(gamma1cut, gamma3) and Equals(gamma1cut,gamma2cut):
       
       xa = GetContextExtensionTyp3(gamma1)
       ya = GetContextExtensionTyp2(gamma1)          
       pxy = GetContextExtensionTyp(gamma1)
       x = xa.left
       y = ya.left
       eq2 = MakeApp3(Leaf("equals","HottTerm"), biga1, x , y) 
       u = GetTypingType(aux1)
       bigc = GetTypingTerm(aux1)
       za = GetContextExtensionTyp(gamma2)
       z = za.left
       c = GetTypingTerm(aux2)
       bigc2 = GetTypingType(aux2)
       p = pxy.left
       reflz = MakeApp(Leaf("refl","HottTerm"), z)
       if Equals(xa.right,ya.right) and Equals(xa.right, biga1):
        
        if Equals(pxy.right,eq2) and Equals(za.right, biga1):
         
         subc = TripleSubstitution(bigc,[x,y,p],[z,z, reflz ])
         
         if Equals(bigc2,subc) and IsUniverse(u):
           
           newc = TripleSubstitution(bigc,[x,y,p],[a,b, p1 ])     
           t = MakeApp6(Leaf("ind","HottTerm"), MakeApp(Leaf("equals","HottTerm"), biga1), MakeLambda3(x,y,p,bigc), MakeLambda(z,c), a,b,p1)
           exp = MakeTyping(gamma3, MakeGenTyp(t, newc ))
           proofelement = ProofElement("EqElim",[ty1,ty2,ty3,ty4,ty5],[], exp)
           proofelement.pos = len(self.proof) + 1
           self.proof.append(proofelement)
           self.log.append("EqElim(" + str(ty1) + ","  + str(ty2)  +  ","  + str(ty3)  +","  + str(ty4) + ","  + str(ty5) +  ")")
           return True          
               
 def EqComp(self, ty1,ty2,ty3):
  aux1 = Proof.proof[ty1].formula
  aux2 = Proof.proof[ty2].formula
  aux3 = Proof.proof[ty3].formula
  
  if aux1.type=="Typing" and aux2.type=="Typing" and aux3.type=="Typing" :
     
    gamma3 = GetTypingContext(aux3)
   
    a = GetTypingTerm(aux3)
   
    biga1 = GetTypingType(aux3)  
     
    gamma1 = GetTypingContext(aux1)
    gamma2 = GetTypingContext(aux2)
    if len(gamma1.children)> 2 and len(gamma2.children)>0:
      
      gamma1cut = Cut3(gamma1)
      gamma2cut = Cut1(gamma2)
      if Equals(gamma1cut, gamma3) and Equals(gamma1cut,gamma2cut):
       
       xa = GetContextExtensionTyp3(gamma1)
       ya = GetContextExtensionTyp2(gamma1)          
       pxy = GetContextExtensionTyp(gamma1)
       x = xa.left
       y = ya.left
       eq2 = MakeApp3(Leaf("equals","HottTerm"), biga1, x , y) 
       u = GetTypingType(aux1)
       bigc = GetTypingTerm(aux1)
       za = GetContextExtensionTyp(gamma2)
       z = za.left
       c = GetTypingTerm(aux2)
       bigc2 = GetTypingType(aux2)
       p = pxy.left
       reflz = MakeApp(Leaf("refl","HottTerm"), z)
       refla = MakeApp(Leaf("refl","HottTerm"), a)
       if Equals(xa.right,ya.right) and Equals(xa.right, biga1):
        
        if Equals(pxy.right,eq2) and Equals(za.right, biga1):
         
         subc = TripleSubstitution(bigc,[x,y,p],[z,z, reflz ])
         
         if Equals(bigc2,subc) and IsUniverse(u):
           
           newc = TripleSubstitution(bigc,[x,y,p],[a,a, refla ])     
           t = MakeApp6(Leaf("ind","HottTerm"), MakeApp(Leaf("equals","HottTerm"), biga1), MakeLambda3(x,y,p,bigc), MakeLambda(z,c), a,a,refla)
           exp = MakeEquiv(gamma3, t, Substitution(c,z,a ), newc )
           proofelement = ProofElement("EqComp",[ty1,ty2,ty3],[], exp)
           proofelement.pos = len(self.proof) + 1
           self.proof.append(proofelement)
           self.log.append("EqComp(" + str(ty1) + ","  + str(ty2)  +  ","  + str(ty3)  +  ")")
 
           return True          
 
 def Subst1(self,left,right,p):
    aux1 = Proof.proof[left].formula
    aux2 = Proof.proof[right].formula
    if aux1.type =="Typing" and aux2.type =="Typing":
     gamma1 = GetTypingContext(aux1)
     gamma2 = GetTypingContext(aux2)
     if p < len(gamma2.children):
      beg = MakeContext(gamma2.children[:p]) 
      end = MakeContext(gamma2.children[p+1:])
      mid = gamma2.children[p]
      a = GetTypingTerm(aux1)
      biga = GetTypingType(aux1)
      b = GetTypingTerm(aux2)
     
      bigb = GetTypingType(aux2)
     if Equals(gamma1,beg) and Equals(biga,mid.right):
        x = mid.left
        newend = Substitution(end,x,a)
        newb = Substitution(b,x,a)
        
        newbigb = Substitution(bigb,x,a)
        exp = MakeTyping(JoinContext(beg,newend), MakeGenTyp(newb,newbigb) )
        proofelement = ProofElement("Subst1",[left,right],[p], exp)
        proofelement.pos = len(self.proof) + 1
        self.proof.append(proofelement)
        self.log.append("Subst1(" + str(left) + ","  + str(right)  +  ","  + str(p)  +  ")")
        return True
 
 
                               
 def Subst2(self,left,right,p):
    aux1 = Proof.proof[left].formula
    aux2 = Proof.proof[right].formula
    if aux1.type =="Typing" and aux2.type =="Equiv":
     gamma1 = GetTypingContext(aux1)
     gamma2 = GetTypingContext(aux2)
     if p < len(gamma2.children):
      beg = MakeContext(gamma2.children[:p]) 
      end = MakeContext(gamma2.children[p+1:])
      mid = gamma2.children[p]
      a = GetTypingTerm(aux1)
      biga = GetTypingType(aux1)
      b = GetEquivLeftTerm(aux2)
      c = GetEquivRightTerm(aux2)
      bigb = GetEquivType(aux2)
     if Equals(gamma1,beg) and Equals(biga,mid.right):
        x = mid.left
        newend = Substitution(end,x,a)
        newb = Substitution(b,x,a)
        newc = Substitution(c,x,a)
        newbigb = Substitution(bigb,x,a)
        exp = MakeEquiv(JoinContext(beg,newend), newb,newc,newbigb)
        proofelement = ProofElement("Subst2",[left,right],[p], exp)
        proofelement.pos = len(self.proof) + 1
        self.proof.append(proofelement)
        self.log.append("Subst2(" + str(left) + ","  + str(right)  +  ","  + str(p)  +  ")")
        return True
           
 def Subst3(self,left,right,pos):
    aux1 = Proof.proof[left].formula
    aux2 = Proof.proof[right].formula
    if aux2.type =="Typing" and aux1.type =="Equiv":
     gamma1 = GetTypingContext(aux1)
     gamma2 = GetTypingContext(aux2)
     if pos < len(gamma2.children):
      beg = MakeContext(gamma2.children[:pos]) 
      end = MakeContext(gamma2.children[pos+1:])
      mid = gamma2.children[pos]
      biga = GetEquivType(aux1)
      a = GetEquivLeftTerm(aux1)
      b = GetEquivRightTerm(aux1)
      c = GetTypingTerm(aux2)
      bigc = GetTypingType(aux2)
     if Equals(gamma1,beg) and Equals(biga,mid.right):
        x = mid.left
        newend = Substitution(end,x,a)
        
        newc1 = Substitution(c,x,a)
        newc2 = Substitution(c,x,b)
        newbigc = Substitution(bigc,x,a)
        exp = MakeEquiv(JoinContext(beg,newend), newc1,newc2,newbigc)
        proofelement = ProofElement("Subst3",[left,right],[pos], exp)
        proofelement.pos = len(self.proof) + 1
        self.proof.append(proofelement)
        self.log.append("Subst3(" + str(left) + ","  + str(right)  +  ","  + str(pos)  +  ")")
        return True
           
 
 def Wkg1(self,left,right,varname,p):
    aux1 = Proof.proof[left].formula
    aux2 = Proof.proof[right].formula
    if aux1.type =="Typing" and aux2.type =="Typing":
     gamma1 = GetTypingContext(aux1)
     gamma2 = GetTypingContext(aux2)
     varl = GetContextVariables(gamma2)
     if p < len(gamma2.children) + 1 and not varname in varl and not varname in parser.constants:
      beg = MakeContext(gamma2.children[:p]) 
      end = MakeContext(gamma2.children[p:]) 
      u = GetTypingType(aux1)
      biga = GetTypingTerm(aux1)
      if IsUniverse(u) and Equals(gamma1,beg):
        t1 = GetTypingGenTyp(aux2)
        t = MakeVarTyp( Leaf(varname,"HottTerm") ,biga)
        g1 = JoinContext(beg,MakeContext([t]))
        gamma = JoinContext(g1,end)
        exp = MakeTyping(gamma,t1)
        if not varname in parser.variables:
         parser.variables.append(varname)
        proofelement = ProofElement("Wkg1",[left,right],[varname,p], exp)
        proofelement.pos = len(self.proof) + 1
        self.proof.append(proofelement)
        self.log.append("Wkg1(" + str(left) + ","  + str(right)  +  ","  + '"'+ varname +'"'  +  "," + str(p) + ")")
        return True
        
 def Wkg2(self,left,right,varname,p):
    aux1 = Proof.proof[left].formula
    aux2 = Proof.proof[right].formula
    if aux1.type =="Typing" and aux2.type =="Equiv":
     gamma1 = GetTypingContext(aux1)
     gamma2 = GetEquivContext(aux2)
     varl = GetContextVariables(gamma2)
     if p < len(gamma2.children) + 1 and not varname in varl and not varname in parser.constants:
      beg = MakeContext(gamma2.children[:p]) 
      end = MakeContext(gamma2.children[p:]) 
      u = GetTypingType(aux1)
      biga = GetTypingTerm(aux1)
      if IsUniverse(u) and Equals(gamma1,beg):
        b = GetEquivLeftTerm(aux2)
        c = GetEquivRightTerm(aux2)
        bigb = GetEquivType(aux2)  

        t = MakeVarTyp( Leaf(varname,"HottTerm"), biga)
        g1 = JoinContext(beg,MakeContext([t]))
        gamma = JoinContext(g1,end)
        exp = MakeEquiv(gamma,b,c, bigb)
        if not varname in parser.variables:
            parser.variables.append(varname)
        proofelement = ProofElement("Wkg2",[left,right],[varname,p], exp)
        proofelement.pos = len(self.proof) + 1
        self.proof.append(proofelement)
        self.log.append("Wkg2(" + str(left) + ","  + str(right)  +  ","  + '"'+ varname +'"'  + "," + str(p) + ")")
        return True
           
                    
     
 def Save(self,name):    
   f = open(name,'wb')
   global variables
   global constants
   data = {"variables":variables, "constants":parser.constants,"proofenv":self}
   pickle.dump(data,f)
   f.close()
   return True

 def NewDef(self,up,name):
     
# The term must be closed ! This eases expression of dependent types as products and functions     
  aux =  Proof.proof[up].formula
  if aux.type=="Typing":
   gamma = GetTypingContext(aux)
   if len(gamma.children) == 0:      
       
     if not name in self.definitions.keys() and not name in parser.constants:
       self.definitions[name] = GetTypingTerm(aux)
       parser.constants.append(name)
       self.log.append("NewDef(" + str(up) + "," + '"' + name + '"' + ")")
       print(name + " := " + Disp2(GetTypingGenTyp(aux), True))
       return True
   
   
 def DefInt(self,up,constant,places):
   if constant in self.definitions.keys():
      const = Leaf(constant,"HottTerm")
      pre = copy.deepcopy(self.proof[up].formula)
      aux2 = copy.deepcopy(self.definitions[constant])
      aux = Position(pre,aux2,0)[0]
      exp = SubstitutionByPosition(Free(aux,[]),Free(aux2,[]),const, places)
      proofelement = ProofElement("DefInt",[up],[constant,places], exp)
      proofelement.pos = len(self.proof) + 1
      self.proof.append(proofelement)
      self.log.append("DefInt(" + str(up) + "," + '"' + constant + '"' +"," + PrintNumList(places) + ")")
      return True                    

 def NewTheorem(self, string):
   if HottExp(string)!=None:
     #must check environment compatibility or impose empty context and mere compatible variable typing  
     proofelement = ProofElement("NewTheorem",[],[string], HottExp(string))
     proofelement.pos = len(self.proof) + 1
     self.proof.append(proofelement)
     self.log.append("NewTheorem(" + '" ' + string + '"'  + ")")
     return True     
     
 def Hyp(self, string):
   if HottExp(string)!=None:
     #must check environment compatibility or impose empty context and mere compatible variable typing  
     proofelement = ProofElement("Hyp",[],[string], HottExp(string))
     proofelement.pos = len(self.proof) + 1
     self.proof.append(proofelement)
     self.log.append("Hyp(" + '" ' + string + '"'  + ")")
     return True     
          

 def ShowLog(self):
  n = 0        
  for l in self.log:
    print(str(n) + ". " + l)
    n = n + 1 
    
    
    
#Cubical Rules

     
 def EquivProj(self,u):
     up = self.proof[u].formula 
     if up.type =="Equiv":
        gamma = GetEquivContext(up)
        ter = GetEquivRightTerm(up)
        typ = GetEquivType(up)
        aux = MakeTyping(gamma, MakeGenTyp(ter,typ))
        proofelement = ProofElement("EquivProj",[u],[], aux)
        proofelement.pos = len(self.proof) + 1
        self.proof.append(proofelement)
        self.log.append("EquivProj("  +  str(u)  +  ")")
        return True   
 
 def TypingContext(self,u):
    up = self.proof[u].formula
    aux = GetTypingContext(up) 
    proofelement = ProofElement("TypingContext",[u],[], aux)
    proofelement.pos = len(self.proof) + 1
    self.proof.append(proofelement)
    self.log.append("TypingContext("  +  str(u)  +  ")")
    return True                             
        
Proof = ProofEnvironment([],"MyProof")            


def Save(name):
 return Proof.Save(name)
 
def ShowProof():
  Proof.ShowProof()
  return True
  
   
def CtxEmp():
  return Proof.CtxEmp()
  
def CtxExt(up,varstring):
  return Proof.CtxExt(up,varstring)
 
def Vble(up,n):
    return Proof.Vble(up,n)

def Refl(up):
    return Proof.Refl(up)

def Sym(up):
    return Proof.Sym(up)
    
def Trans(left,right):    
    return Proof.Trans(left,right)
    
def Equiv1(left,right):    
    return Proof.Equiv1(left,right)
        
def Equiv2(left,right):    
    return Proof.Equiv2(left,right)
            
    
def UIntro(up,i):
    return Proof.UIntro(up,i)
    
    
def UCumul(up):    
    return Proof.UCumul(up) 
       
def PiIntro(up):
    return Proof.PiIntro(up)   
    
def PiForm(left,right):
    return Proof.DepForm(left,right, "Pi") 
    
def SigmaForm(left,right):
    return Proof.DepForm(left,right, "Sigma") 
         
    
def PiElim(left,right):
    return Proof.PiElim(left,right)  
    
def PiComp(left,right):        
    return Proof.PiComp(left,right)
    
def PiUniq(up):    
    return Proof.PiUniq(up)
    
def SigmaIntro(up, left, right):    
    return Proof.SigmaIntro( up, left, right)
    

def SigmaElim(up,left,right):         
    return Proof.SigmaElim(up,left,right)  
    
    
def SigmaComp(up, left,right1,right2):           
    return Proof.SigmaComp(up, left,right1,right2 )

def PlusForm(left,right):
    return Proof.PlusForm(left,right)
    
def PlusIntro1(left,right,up):
    return Proof.PlusIntro(left,right,up,1)
    
def PlusIntro2(left,right,up):
    return Proof.PlusIntro(left,right,up,2)
    
def PlusElim(down,left,right,up):
    return Proof.PlusElim(down,left,right,up)
    
def PlusComp1(down,left,right,up):
    return Proof.PlusComp(down,left,right,up,1)        
            
def PlusComp2(down,left,right,up):
    return Proof.PlusComp(down,left,right,up,2)
            
def OForm(up,i):
    return Proof.OForm(up,i)    

def OElim(left,right):
    return Proof.OElim(left,right)

    
def NatForm(up,i):
    return Proof.NatForm(up,i)
    
def NatIntro1(up):
    return Proof.NatIntro1(up)
    
def NatIntro2(up):
    return Proof.NatIntro2(up)
                
def NatElim( up,left,right,down): 
    return Proof.NatElim(up,left,right,down)

 
def NatComp1( up,left,right):
    return Proof.NatComp1(up,left,right)
    
def NatComp2( up,left,right,down): 
     return Proof.NatComp2(up,left,right,down)   
 
def EqForm(left,center,right): 
    return Proof.EqForm(left,center,right)
 
def EqIntro(left,right):
    return Proof.EqIntro(left,right)   
    
def EqElim(ty1,ty2,ty3,ty4,ty5):                
    return Proof.EqElim(ty1,ty2,ty3,ty4,ty5)

def EqComp(ty1,ty2,ty3):    
    return Proof.EqComp(ty1,ty2,ty3)
    
    
def Subst1(left,right,pos):   
    return Proof.Subst1(left,right,pos)    
   
def Subst2(left,right,pos):   
    return Proof.Subst2(left,right,pos)
  
def Subst3(left,right,pos):  
    return Proof.Subst3(left,right,pos)
    
def Wkg1(left,right,varname,pos):
    return Proof.Wkg1(left,right,varname,pos)
    
def Wkg2(left,right,varname,pos):
    return Proof.Wkg2(left,right,varname,pos)        
        
def NewDef(up,name):
    return Proof.NewDef(up,name)    
    
def DefInt(up,constant,places):
    return Proof.DefInt(up,constant,places)    


    
    
def EquivProj(u):  
    return Proof.EquivProj(u)  
    
def TypingContext(u):    
    return Proof.TypingContext(u)
    
    

    
#legacy
def NewTheorem(string):
   return Proof.NewTheorem(string)
 
def Hyp(string):
   return Proof.Hyp(string)   
 
def ShowLog():
    return Proof.ShowLog()   

def Load(name):
 global Proof    
 f = open(name,'rb')
 data = pickle.load(f)
 Proof = data["proofenv"]
 global variables
 global constants

 parser.variables = data["variables"]
 
 parser.constants = data["constants"]
 constants = parser.constants
 f.close()
 
 return True
 
def GenerateProof():
  global variables
  for v in variables:
   if '_' in v:
    variables.remove(v)    
  Proof.proof = [] 
  aux = Proof.log
  Proof.log = [] 
  Proof.definitions = {}
  
  global constants
  global initvars
  global initconsts
  variables = copy.deepcopy(initvars)
  constants = copy.deepcopy(initconsts)
  parser.variables = variables
  parser.constants = constants         
  for logelem in aux:
                
  
     exec(logelem)
  
 # if len(Proof.proof)>0: 
  # last = len(Proof.proof)-1
  # Proof.Qed(last) 
  ShowProof() 
                
 
def Undo():
    Proof.log.pop()
    for v in variables:
     if '_' in v:
      variables.remove(v)
    GenerateProof()
    return True 

print("")
print("Welcome to PyHott 1.0") 
print("")
print("Homotopy Type Theory Proof Assistant and Proof Checker")
print("")
print("(c) 2022  C. Lewis Protin")
print("")

