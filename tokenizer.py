def PrintNumList(list):
 out = "[" 
 for x in list:
  out = out + str(x) + ","
 out1 = out[:len(out)-1]
 return out1 +"]"

def SpaceParenthesis(form):
  if form == None or form =="":
   return ""
  if form[0] in ["(",")",",",".",":","=","*"]:
   return " " + form[0] + " " +SpaceParenthesis(form[1:])
  else:
   return form[0] + SpaceParenthesis(form[1:])

def Dash(form):     
  if form == None or form =="":
   return ""
  if form [0:2]=="|-":
    return " "+ form[0:2] + " "+ Dash(form[2:])
  else:
   return form[0] + Dash(form[1:])

def Clean(f):
 def aux(form):
  if form[0]==" ":
    return form[1:]
  if form[len(form)-1]==" ":
    return form[0:len(form)-1]
  for i in range(0,len(form)-1):
   if form[i:i+2] =="  ":
     return form[0:i] + form[i+1:]
  return form
 while f!=aux(f):
  f = aux(f)
 return f

def Fix(form):
 return Clean(Dash(SpaceParenthesis(form))) 

def Tokenize(form):
 aux = Fix(form).split(" ")
 if aux[0]=="|-":
  return ["."] +aux
 return aux 
 
alphabet = ["a","b","c","d","e","f","g","h","i","j","k","l","m","n","o","p","q","r","s","t","u",
"v","w","x","y","z", "A","B","C","D","E","F","G","H","I","J","K","L","M","N","O","P","Q","R","S","T","U","V",
"W","X","Y","Z"]

varmax = 1000

def Fresh(state,alphabet):
 for a in alphabet:
  if not a in state:
    return a
 for n in range(0,varmax):
  if not "x_"+str(n) in state:
   return "x_"+str(n)
  
def ParenthesisGen(list,symb):
  if len(list) < 2:
    return None    
  if len(list) == 2:
    return "(" + list[0] + symb + list[1] + ")"
  else:
    return  "(" + list[0] + symb + ParenthesisGen(list[1: ],symb) + ")"        
          