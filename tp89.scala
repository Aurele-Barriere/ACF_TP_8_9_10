package validator.BarriereHutin
import bank._


// Automatic conversion of bank.message to tp89.messages and Nat to bank.Nat
object Converter{
  implicit def bank2message(m:bank.message):tp89.message=
    m match {
    case bank.Pay((bank.Nat.Nata(c),(bank.Nat.Nata(m),bank.Nat.Nata(i))),bank.Nat.Nata(p)) => tp89.Pay((Nat.Nata(c),(Nat.Nata(m),Nat.Nata(i))),Nat.Nata(p))
    case bank.Ack((bank.Nat.Nata(c),(bank.Nat.Nata(m),bank.Nat.Nata(i))),bank.Nat.Nata(p)) => tp89.Ack((Nat.Nata(c),(Nat.Nata(m),Nat.Nata(i))),Nat.Nata(p))
    case bank.Cancel((bank.Nat.Nata(c),(bank.Nat.Nata(m),bank.Nat.Nata(i)))) => tp89.Cancel((Nat.Nata(c),(Nat.Nata(m),Nat.Nata(i))))
  }
  
  implicit def trans2bankTrans(l:List[((Nat.nat,(Nat.nat,Nat.nat)),Nat.nat)]): List[((bank.Nat.nat,(bank.Nat.nat,bank.Nat.nat)),bank.Nat.nat)]=
    l match {
    case Nil => Nil
    case ((Nat.Nata(c),(Nat.Nata(m),Nat.Nata(i))),Nat.Nata(p))::r => ((bank.Nat.Nata(c),(bank.Nat.Nata(m),bank.Nat.Nata(i))),bank.Nat.Nata(p))::trans2bankTrans(r)
  }
}

import Converter._


/* The object to complete */ 
class ConcreteValidator extends TransValidator{


  
  // creating a database
  var db = List.empty[((Nat.nat, (Nat.nat, Nat.nat)),(tp89.status, (Option[Nat.nat], Option[Nat.nat])))]
  
	// TODO
	def process(m:message){
    db = tp89.traiterMessage(m,db)
  }

	// TODO
	def getValidTrans: List[((Nat.nat, (Nat.nat, Nat.nat)),Nat.nat)]= tp89.export(db)

	// TODO
	def authors= "BarriereHutin"
}







// imported from isabelle
/*
object HOL {

trait equal[A] {
  val `HOL.equal`: (A, A) => Boolean
}
def equal[A](a: A, b: A)(implicit A: equal[A]): Boolean = A.`HOL.equal`(a, b)

def eq[A : equal](a: A, b: A): Boolean = equal[A](a, b)

} /* object HOL */

object Nat {

abstract sealed class nat
final case class zero_nat() extends nat
final case class Suc(a: nat) extends nat

def equal_nata(x0: nat, x1: nat): Boolean = (x0, x1) match {
  case (zero_nat(), Suc(x2)) => false
  case (Suc(x2), zero_nat()) => false
  case (Suc(x2), Suc(y2)) => equal_nata(x2, y2)
  case (zero_nat(), zero_nat()) => true
}

implicit def equal_nat: HOL.equal[nat] = new HOL.equal[nat] {
  val `HOL.equal` = (a: nat, b: nat) => equal_nata(a, b)
}

def less_eq_nat(x0: nat, n: nat): Boolean = (x0, n) match {
  case (Suc(m), n) => less_nat(m, n)
  case (zero_nat(), n) => true
}

def less_nat(m: nat, x1: nat): Boolean = (m, x1) match {
  case (m, Suc(n)) => less_eq_nat(m, n)
  case (n, zero_nat()) => false
}

} /* object Nat */
*/
object Product_Type {

def equal_proda[A : HOL.equal, B : HOL.equal](x0: (A, B), x1: (A, B)): Boolean =
  (x0, x1) match {
  case ((x1, x2), (y1, y2)) => HOL.eq[A](x1, y1) && HOL.eq[B](x2, y2)
}

implicit def equal_prod[A : HOL.equal, B : HOL.equal]: HOL.equal[(A, B)] = new
  HOL.equal[(A, B)] {
  val `HOL.equal` = (a: (A, B), b: (A, B)) => equal_proda[A, B](a, b)
}

} /* object Product_Type */

object tp89 {

import /*implicits*/ Product_Type.equal_prod, Nat.equal_nat

abstract sealed class status
final case class Cancelled() extends status
final case class Accepted() extends status
final case class Current() extends status

abstract sealed class message
final case class Pay(a: (Nat.nat, (Nat.nat, Nat.nat)), b: Nat.nat) extends
  message
final case class Ack(a: (Nat.nat, (Nat.nat, Nat.nat)), b: Nat.nat) extends
  message
final case class Cancel(a: (Nat.nat, (Nat.nat, Nat.nat))) extends message

def export(x0: List[((Nat.nat, (Nat.nat, Nat.nat)),
                      (status, (Option[Nat.nat], Option[Nat.nat])))]):
      List[((Nat.nat, (Nat.nat, Nat.nat)), Nat.nat)]
  =
  x0 match {
  case Nil => Nil
  case (tid, (Accepted(), (Some(x), Some(y)))) :: t => (tid, x) :: export(t)
  case (v, (Cancelled(), vc)) :: t => export(t)
  case (v, (Current(), vc)) :: t => export(t)
  case (v, (vb, (None, ve))) :: t => export(t)
  case (v, (vb, (vd, None))) :: t => export(t)
}

def gtOption(n: Nat.nat, x1: Option[Nat.nat]): Boolean = (n, x1) match {
  case (n, None) => true
  case (n, Some(m)) => Nat.less_nat(m, n)
}

def ltOption(n: Nat.nat, x1: Option[Nat.nat]): Boolean = (n, x1) match {
  case (n, None) => true
  case (n, Some(m)) => Nat.less_nat(n, m)
}

def maxOption(n: Nat.nat, x1: Option[Nat.nat]): Nat.nat = (n, x1) match {
  case (n, None) => n
  case (n, Some(b)) => (if (Nat.less_nat(b, n)) n else b)
}

def minOption(n: Nat.nat, x1: Option[Nat.nat]): Nat.nat = (n, x1) match {
  case (n, None) => n
  case (n, Some(b)) => (if (Nat.less_nat(n, b)) n else b)
}

def findTransid(uu: (Nat.nat, (Nat.nat, Nat.nat)),
                 x1: List[((Nat.nat, (Nat.nat, Nat.nat)),
                            (status, (Option[Nat.nat], Option[Nat.nat])))]):
      Option[((Nat.nat, (Nat.nat, Nat.nat)),
               (status, (Option[Nat.nat], Option[Nat.nat])))]
  =
  (uu, x1) match {
  case (uu, Nil) => None
  case (tid, (tid2, (s, (o1, o2))) :: t) =>
    (if (Product_Type.equal_proda[Nat.nat, (Nat.nat, Nat.nat)](tid, tid2))
      Some[((Nat.nat, (Nat.nat, Nat.nat)),
             (status,
               (Option[Nat.nat], Option[Nat.nat])))]((tid2, (s, (o1, o2))))
      else findTransid(tid, t))
}

def isAcceptable(x0: (Option[Nat.nat], Option[Nat.nat])): Boolean = x0 match {
  case (Some(x1), Some(x2)) =>
    (if (Nat.less_eq_nat(x2, x1) && Nat.less_nat(Nat.zero_nat, x1)) true
      else false)
  case (None, va) => false
  case (v, None) => false
}

def removeTransid(uu: (Nat.nat, (Nat.nat, Nat.nat)),
                   x1: List[((Nat.nat, (Nat.nat, Nat.nat)),
                              (status, (Option[Nat.nat], Option[Nat.nat])))]):
      List[((Nat.nat, (Nat.nat, Nat.nat)),
             (status, (Option[Nat.nat], Option[Nat.nat])))]
  =
  (uu, x1) match {
  case (uu, Nil) => Nil
  case (tid, (tid2, (s, (o1, o2))) :: t) =>
    (if (Product_Type.equal_proda[Nat.nat, (Nat.nat, Nat.nat)](tid, tid2)) t
      else (tid2, (s, (o1, o2))) :: removeTransid(tid, t))
}

def traiterMessage(x0: message,
                    bdd: List[((Nat.nat, (Nat.nat, Nat.nat)),
                                (status, (Option[Nat.nat], Option[Nat.nat])))]):
      List[((Nat.nat, (Nat.nat, Nat.nat)),
             (status, (Option[Nat.nat], Option[Nat.nat])))]
  =
  (x0, bdd) match {
  case (Cancel(tid), bdd) =>
    (findTransid(tid, bdd) match {
       case None => (tid, (Cancelled(), (None, None))) :: bdd
       case Some((_, (_, (_, _)))) =>
         {
           val a: List[((Nat.nat, (Nat.nat, Nat.nat)),
                         (status, (Option[Nat.nat], Option[Nat.nat])))]
             = removeTransid(tid, bdd);
           (tid, (Cancelled(), (None, None))) :: a
         }
     })
  case (Pay(tid, x), bdd) =>
    (findTransid(tid, bdd) match {
       case None => (tid, (Current(), (Some[Nat.nat](x), None))) :: bdd
       case Some((_, (Cancelled(), (_, _)))) => bdd
       case Some((_, (Accepted(), (_, _)))) => bdd
       case Some((_, (Current(), (o1, o2)))) =>
         (if (gtOption(x, o1))
           {
             val bdd2: List[((Nat.nat, (Nat.nat, Nat.nat)),
                              (status, (Option[Nat.nat], Option[Nat.nat])))]
               = removeTransid(tid, bdd)
             val m: Nat.nat = maxOption(x, o1);
             (if (isAcceptable((Some[Nat.nat](m), o2)))
               (tid, (Accepted(), (Some[Nat.nat](m), Some[Nat.nat](m)))) :: bdd2
               else (tid, (Current(), (Some[Nat.nat](m), o2))) :: bdd2)
           }
           else bdd)
     })
  case (Ack(tid, x), bdd) =>
    (findTransid(tid, bdd) match {
       case None => (tid, (Current(), (None, Some[Nat.nat](x)))) :: bdd
       case Some((_, (Cancelled(), ba))) => bdd
       case Some((_, (Accepted(), ba))) => bdd
       case Some((_, (Current(), (o1, o2)))) =>
         (if (ltOption(x, o2))
           {
             val bdd2: List[((Nat.nat, (Nat.nat, Nat.nat)),
                              (status, (Option[Nat.nat], Option[Nat.nat])))]
               = removeTransid(tid, bdd)
             val m: Nat.nat = minOption(x, o2);
             (if (isAcceptable((o1, Some[Nat.nat](m))))
               (tid, (Accepted(), (o1, o1))) :: bdd2
               else (tid, (Current(), (o1, Some[Nat.nat](m)))) :: bdd2)
           }
           else bdd)
     })
}

} /* object tp89 */

