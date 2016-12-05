theory tp89bis
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


datatype status = Cancelled | Accepted | Current

(* the 1st nat option is the highest price from the buyer
   the 2nd nat option is the lowest price from the seller *)
type_synonym transBdd = "(transid * status * (nat option) * (nat option)) list" 


(* returns true if an element is in a list *)
fun member :: "'a \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "member _ [] = False" |
  "member x (h#t) = (if x=h then True else member x t)"

(* same for a list of couples when looking among the left part *)
fun memberLeft :: "'a \<Rightarrow> ('a * 'b) list \<Rightarrow> bool"
where
  "memberLeft _ [] = False" |
  "memberLeft x ((h,_)#t) = (if x=h then True else memberLeft x t)"


(* checks that a list of coubles never has the same left element *)
fun noDoubleLeft :: "('a * 'b) list \<Rightarrow> bool"
where
  "noDoubleLeft [] = True" |
  "noDoubleLeft ((a, _)#t) = (if memberLeft a t then False else noDoubleLeft t)"


(* exports the list of validated transactions *)
fun export :: "transBdd \<Rightarrow> transaction list"
where
  "export [] = []" |
  "export ((tid, Accepted, Some x, Some y)#t) = (tid, x)#(export t)" |
  "export (_#t) = (export t)"

(* finds a transid, its status and the options from a transBdd *)
fun findTransid :: "transid \<Rightarrow> transBdd \<Rightarrow> (transid * status * (nat option) * (nat option)) option"
where
  "findTransid _ [] = None" |
  "findTransid tid ((tid2, s, o1, o2)#t) = (if tid=tid2 then Some (tid2, s, o1, o2) else findTransid tid t)"


(* remove the only transaction indexed by transid from the db *)
fun removeTransid :: "transid \<Rightarrow> transBdd \<Rightarrow> transBdd"
where
  "removeTransid _ [] = []" |
  "removeTransid tid ((tid2, s, o1, o2)#t) = (if tid=tid2 then t else (tid2, s, o1, o2)#(removeTransid tid t))"


(* options operators *)
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
  "gteOption n None = True" |
  "gteOption n (Some m) = (n\<ge>m)"


fun gtOption :: "nat \<Rightarrow> nat option \<Rightarrow> bool"
where
  "gtOption n None = True" |
  "gtOption n (Some m) = (n>m)"

fun lteOption :: "nat \<Rightarrow> nat option \<Rightarrow> bool"
where
  "lteOption n None = True" |
  "lteOption n (Some m) = (n\<le>m)"


fun ltOption :: "nat \<Rightarrow> nat option \<Rightarrow> bool"
where
  "ltOption n None = True" |
  "ltOption n (Some m) = (n<m)"

(* takes a buyer option, a seller option and returns true if it is an acceptable transaction *)
fun isAcceptable :: "((nat option) * (nat option)) \<Rightarrow> bool"
where
"isAcceptable (Some x1, Some x2) = (if ((x1 \<ge> x2) \<and> (x1 > 0)) then True else False)" |
" isAcceptable _ = False"

(* updates a transBdd with a message *)
fun traiterMessage :: "message \<Rightarrow> transBdd \<Rightarrow> transBdd"
where
  "traiterMessage (Cancel tid) bdd = 
    (let r = findTransid tid bdd in
      (case r of  
        None \<Rightarrow> (tid, Cancelled, None, None)#bdd |
        Some (tid2, s, o1, o2) \<Rightarrow> let bdd2 = removeTransid tid bdd in
                                  (tid, Cancelled, None, None)#bdd2
      )
    )" |
  "traiterMessage (Pay tid x) bdd =
    (let r = findTransid tid bdd in
      (case r of
        None \<Rightarrow> (tid, Current, Some x, None)#bdd |
        Some (tid2, Current, o1, o2) \<Rightarrow> (if gtOption x o1 then
                                          let bdd2 = removeTransid tid bdd in
                                          let m = maxOption x o1 in
                                          if isAcceptable(Some m, o2) then (tid, Accepted, Some m, Some m)#bdd2
                                          else (tid, Current, Some m, o2)#bdd2
                                        else
                                        bdd) |
        Some (tid2, _, o1, o2) \<Rightarrow> bdd
      )
    )"|
    "traiterMessage (Ack tid x) bdd =
    (let r = findTransid tid bdd in
    (case r of 
      None \<Rightarrow> (tid,Current,None,Some x)#bdd |
      Some (tid2, Current, o1, o2) \<Rightarrow> (if ltOption x o2 then
                                        let bdd2 = removeTransid tid bdd in
                                        let m = minOption x o2 in
                                        if isAcceptable(o1,Some m) then (tid,Accepted,o1,o1)#bdd2
                                        else (tid,Current,o1, Some m)#bdd2
                                       else bdd) |
      _ \<Rightarrow> bdd ))"

(* updates in an accumulator *)
fun traiterMessageListAcc :: "message list \<Rightarrow> transBdd \<Rightarrow> transBdd"
where
"traiterMessageListAcc [] bdd = bdd" |
"traiterMessageListAcc (h#t) bdd = traiterMessageListAcc t (traiterMessage h bdd)"

(* constructs the bdd from a message list. head of the list = first message treated *)
fun traiterMessageList :: "message list \<Rightarrow> transBdd"
where
"traiterMessageList l = traiterMessageListAcc l []"



(* Correction properties *)
lemma prop1 : "\<forall> tid x l . member (tid, x) (export (traiterMessageList l)) \<longrightarrow> (x > 0)"
quickcheck
nitpick
sorry

lemma prop2 : "\<forall> l . noDoubleLeft (export (traiterMessageList l))"
quickcheck
nitpick
sorry

lemma prop3 : "\<forall> tid l . member (tid, Cancelled, None, None) (traiterMessage (Cancel tid) (traiterMessageList l))"
quickcheck
nitpick
sorry


lemma prop4 : "\<forall> tid l . member (Cancel tid) l \<longrightarrow> \<not>memberLeft tid (export (traiterMessageList l))"
quickcheck
nitpick
sorry

lemma prop5 : "\<forall> tid l buyer seller. member (Pay tid buyer) l \<longrightarrow> member (Ack tid seller) l \<longrightarrow> buyer \<ge> seller \<longrightarrow> buyer > 0 \<longrightarrow> \<not> member (Cancel tid) l \<longrightarrow> memberLeft tid (export (traiterMessageList l))"
quickcheck
nitpick
sorry

lemma prop6 : "\<forall> tid l. memberLeft tid (export(traiterMessageList l)) \<longrightarrow> (\<exists> buyer seller. (member (Pay tid buyer) l) \<and> (member (Ack tid seller) l) \<and> buyer\<ge>seller)"
quickcheck
nitpick
sorry

lemma prop7 : "\<forall> tid l l2 buyerhigh buyerlow x. 
              member (Pay tid buyerhigh) l 
              \<longrightarrow> buyerhigh \<ge> buyerlow 
              \<longrightarrow> ~(member (Cancel tid) l2)
              \<longrightarrow> ((member (tid,x) (export(traiterMessageList (l@((Pay tid buyerlow)#l2))))) \<longleftrightarrow> (member (tid,x) (export(traiterMessageList (l@l2)))))"
quickcheck
nitpick
sorry

lemma prop7' : "\<forall> tid l l2 sellerhigh sellerlow x. 
              member (Ack tid sellerlow) l 
              \<longrightarrow> sellerhigh \<ge> sellerlow 
              \<longrightarrow> ~(member (Cancel tid) l2)
              \<longrightarrow> ((member (tid,x) (export(traiterMessageList (l@((Ack tid sellerhigh)#l2))))) \<longleftrightarrow> (member (tid,x) (export(traiterMessageList (l@l2)))))"
quickcheck
nitpick
sorry


lemma prop8 : "\<forall> tid l1 l2 x x2 . member (tid,x) (export(traiterMessageList(l1))) \<longrightarrow> member (tid,x2) (export(traiterMessageList(l1 @ l2))) \<longrightarrow> x=x2"
quickcheck
nitpick
sorry

lemma prop9 : "\<forall> x tid l. member (tid,x) (export(traiterMessageList l)) \<longrightarrow> (member (Pay tid x) l)"
quickcheck
nitpick
sorry


(* ----- Exportation en Scala (Isabelle 2014) -------*)
(* Directive d'exportation *)
export_code export traiterMessage in Scala



end

