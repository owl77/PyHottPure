var SpaceParenthesis = function spaceParenthesis(form){
  if ((form == null) || form ==""){
   return ""}
  if (["(",")",",",".",":","=","*"].includes(form[0])){
   return " " + form[0] + " " +spaceParenthesis(form.slice(1,))}
  else{
   return form[0] + spaceParenthesis(form.slice(1,))} }



function Leaf(value,type){
this.name = "Leaf"
this.type = type
this. value = value
this.free = true
this.pos = -1
this.variable = null}

function Constructor(operator,type,children){     
   this.name ="Constructor"
   this.operator = operator
   this.type= type
   this.children = children
   this.left = null
   this.right = null
   if(children.length ==2){
    this.binary = true
    this.left = children[0]
    this.right = children[1]}}
    
    
var Star = function star(parser,separator){
     var out = function(exp){
      parse = parser(exp)      
      if(parse!=null){
       return [parse] } 
      if (exp.length < 3){
       return null}
      for (let i =0; i < exp.length-1; i++){  
        par1 =  parser(exp.slice(0,i))   
        if (par1== null){
         continue}
        if !!separator.includes(exp[i]){
         continue}
        par2 =  star(parser,separator)(exp.slice(i+1:))
        if (par2 == null){
         continue}
         return [par1] + par2}}
         return out}

