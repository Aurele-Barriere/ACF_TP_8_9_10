theory tp89
imports Main (* "~~/src/HOL/Library/Code_Target_Nat" *)
begin

(* 
quickcheck_params [size=6,tester=narrowing,timeout=120]
nitpick_params [timeout=120]
*)

type_synonym transid= "nat*nat*nat"

datatype message= 
  Pay transid nat  
| Ack transid nat
| Cancel transid

type_synonym transaction= "transid * nat"

type_synonym cancelled = "transid list" (* cancelled transactions *)
type_synonym accepted = "transaction list" (* accepted transactions *)

(* a transaction being treated : its id, the lowest amount from the buyer, the highest from the seller*)
type_synonym current = "(transid * ((nat option) * (nat option))) list" 

type_synonym transBdd= "cancelled * accepted * current" 




fun member :: "'a \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "member _ [] = False" |
  "member x (h#t) = (if x=h then True else member x t)"


fun memberLeft :: "'a \<Rightarrow> ('a * 'b) list \<Rightarrow> bool"
where
  "memberLeft _ [] = False" |
  "memberLeft x ((h,_)#t) = (if x=h then True else memberLeft x t)"


(* Remove an element from a list without doubles *)
fun remove :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "remove _ [] = []" |
  "remove x (h#t) = (if x=h then t else h#(remove x t))"

fun removeLeft :: "'a \<Rightarrow> ('a * 'b) list \<Rightarrow> ('a * 'b) list"
where
  "removeLeft _ [] = []" |
  "removeLeft x ((h,blop)#t) = (if x=h then t else (h,blop)#(removeLeft x t))"


fun export :: "transBdd \<Rightarrow> accepted"
where
  "export (c, a, cur) = a"

fun getCurrent :: "transid \<Rightarrow> current \<Rightarrow> ((nat option) * (nat option))"
where
"getCurrent _ [] = (None,None)" |
"getCurrent trid ((h,(b,s))#t) = (if (trid=h) then (b,s) else getCurrent trid t)"



fun maxOption :: "nat \<Rightarrow> nat option \<Rightarrow> nat"
where
  "maxOption n None = n" |
  "maxOption n (Some b) = (if n > b then n else b)"


fun minOption :: "nat \<Rightarrow> nat option \<Rightarrow> nat"
where
  "minOption n None = n" |
  "minOption n (Some b) = (if n < b then n else b)"
 

fun gteOption :: "nat \<Rightarrow> nat option \<Rightarrow> bool"
where
  "gteOption n None = False" |
  "gteOption n (Some m) = (n\<ge>m)"

fun lteOption :: "nat \<Rightarrow> nat option \<Rightarrow> bool"
where
  "lteOption n None = False" |
  "lteOption n (Some m) = (n\<le>m)"


fun traiterMessage :: "message \<Rightarrow> transBdd \<Rightarrow> transBdd"
where
  "traiterMessage (Cancel trid) (c, a, cur) = (if memberLeft trid a then 
                                              let newa = removeLeft trid a in
                                              let newc = trid#c in
                                              (newc,newa,cur) else 
                                              (if memberLeft trid cur then
                                              let newcur = removeLeft trid cur in
                                              let newc = trid#c in
                                              (newc,a,newcur) else (c,a,cur)))" |
  "traiterMessage (Pay trid n) (c,a,cur) = 
(if (~member trid c \<and> ~memberLeft trid a) then (* the transaction should'nt be negociated when accepted or cancelled *)  
    (if (~memberLeft trid cur) then (* new transaction *)
       let newcur = (trid, (Some(n),None))#cur in
       (c,a,newcur) else (* the transaction already exists *)
       let (b,s) = getCurrent trid cur in
       let m = maxOption n b in
       if gteOption m s then (* the transaction should be accepted *)
           let newcur = (removeLeft trid cur
        
                                           
"                                      





(* ----- Exportation en Scala (Isabelle 2014) -------*)

(* Directive d'exportation *)
export_code export traiterMessage in Scala



end

