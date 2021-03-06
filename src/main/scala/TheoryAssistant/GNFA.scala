//::::::::::::::::::::::::::::::::::::::::::::::
/** Author: Nick Klepp
 *  Date: June 6, 2017
 *  The GNFA object represents a Generalized Non-Deterministic Finite Automaton
 */

package TheoryAssistant

import scala.collection.mutable.{Set,Map}
import TypeDefs._

object GNFA{

       val DEBUG = false

       def convert( m : DFA ) : RegEx =
       {
	   if (DEBUG) println(s"Converting the following DFA to a RegEx: $m")
	   val gnfa = new GNFA(m)
	   if (DEBUG) println(s"Converting $gnfa")
	   convert2(gnfa)
       }

       def convert( m : NFA ) : RegEx = convert(m.DFAify())

       def convert2( m : GNFA ) : RegEx =
       {
	   if (DEBUG) println(s"Converting the following machine: $m")
	   if ( m.getStates.size == 2 ){

	      if (DEBUG) println("Finished converting.")
	      val start = m.getStart()
	      val accept = m.getAccept()
	      var ret = m.getDelta()(start,accept)
	      if ( ret.length == 0 ) ret = "\u2205"
	      return ret
	   }

	      //::::::::::::::::::::::::::::::::::::::::::::::::::::::::::://
	      /*		Grab the state to delete		   */
	      //::::::::::::::::::::::::::::::::::::::::::::::::::::::::::://

	   val qRip = ( m.getStates() -- Set( m.getStart() , m.getAccept() ) ).head
	   if (DEBUG) println(s"Ripping the following state: $qRip")

	      //::::::::::::::::::::::::::::::::::::::::::::::::::::::::::://
	      /*	Make the new set of states and name but keep	   */
	      /*	the old start and accept state and alphabet.       */
	      //::::::::::::::::::::::::::::::::::::::::::::::::::::::::::://

	   val states   = m.getStates() - qRip
	   val alphabet = m.getAlphabet()
	   val delta    = Map[(State,State),RegEx]()
      	   val start    = m.getStart()
      	   val accept   = m.getAccept()
      	   val name     = m.getName() + p

	   if (DEBUG) {
	      println(s"new states will be: $states")
	      println(s"new alphabet will be : $alphabet")
	      println(s"new start will be: $start")
	      println(s"new accept will be: $accept")
	      println(s"new name will be: $name")
	   } // DEBUG

	   val oldDelta    = m.getDelta()

	      //::::::::::::::::::::::::::::::::::::::::::::::::::::::::::://
	      /*	Make the new delta for the new set of states       */
	      //::::::::::::::::::::::::::::::::::::::::::::::::::::::::::://


	   for ( qi <- (m.getStates() -- Set(accept,qRip)) ; qj <- (m.getStates() -- Set(start,qRip)) ) {

	       val in1 = (qi,qRip)
	       val in2 = (qRip,qRip)
	       val in3 = (qRip,qj)
	       val in4 = (qi,qj)

	       if (DEBUG) {
	       	  val OR1 = oldDelta(in1)
		  val OR2 = oldDelta(in2)
		  val OR3 = oldDelta(in3)
	       	  println(s"(qi, qj) : $in4")
		  println(s"(qi,qRip) : $in1 \n(qRip,qRip) :$in2 \n(qRip,qj): $in3")
		  println(s"Old map has the following transitions: \n$in1 -> $OR1 \n$in2 -> $OR2 \n$in3 -> $OR3")
	       } // DEBUG

	       /*
	       var R1  = oldDelta.getOrElse(in1,"")
	       var R2  = oldDelta.getOrElse(in2,"")
	       var R3  = oldDelta.getOrElse(in3,"")
	       */
	       var R1 = oldDelta(in1)
	       var R2 = oldDelta(in2)
	       var R3 = oldDelta(in3)
	       var R4 = oldDelta(in4)

	       R2 = if ( !(R2.equals(NullRegEx) ) ) { if ( starExpr(R2) || unionExpr(R2) ) s"( $R2 )*" else s"$R2*"} else epsilon

	       delta += ( (qi,qj) -> regExUnion(R4,regExCat(R1,regExCat(R2,R3))) )

	   } // for qi , qj

	   convert2(new GNFA(states,alphabet, delta, start, accept, name))
       } // convert2

       private def regExUnion(r1 : RegEx , r2 : RegEx) : RegEx =
       {
           if      ( r1.equals(NullRegEx) ) r2
	   else if ( r2.equals(NullRegEx) ) r1
	   else      		         s"$r1 $Union $r2"
       } // regExUnion

       private def regExCat(r1 : RegEx , r2 : RegEx) : RegEx =
       {
	   if      ( r1.equals(epsilon) ) return r2
	   else if ( r2.equals(epsilon) ) return r1
	   else if ( r1.equals(NullRegEx) || r2.equals(NullRegEx) ) return NullRegEx
	   else{
		val (u1,u2) = unionExprs(r1,r2)
		val (p1,p2) = parentheticExprs(r1,r2)
		(p1,p2) match{
			case (true,true)   => return r1+r2
			case (true,false)  => if ( u2 ) return s"$r1 ( $r2 )" else return r1 + r2
			case (false,true)  => if ( u1 ) return s"( $r1 ) $r2" else return r1 + r2
			case (false,false) => (u1,u2) match{
			     		      	      case (true,true)   => return s"( $r1 )( $r2 )"
						      case (true,false)  => return s"( $r1 ) $r2"
						      case (false,true)  => return s"$r1 ( $r2 )"
						      case (false,false) => return r1+r2
			     		      } // match (u1,u2)
		} // match (p1,p2)
	   } // else
       } // regExCat

       private def parentheticExpr(r : RegEx) : Boolean =
       {
	   var ret = false
	   val rl1 = r.length-1
	   val rl2 = r.length-2
	   r.length match{
	   	    case 0 => ret = true
		    case 1 => ret = true
		    case _ => ret = if ( r.charAt(0) == '(' && ( r.charAt(rl1) == ')' || r.charAt(rl1)=='*' && r.charAt(rl2)==')' ) ) true else false
	   } // match
	   ret
       } // parentheticExpr

       private def parentheticExprs( r1 : RegEx , r2 : RegEx ) : (Boolean,Boolean) = (parentheticExpr(r1),parentheticExpr(r2))

       private def unionExpr(r : RegEx) : Boolean = r.contains(Union)
       private def unionExprs(r1 : RegEx, r2 : RegEx) : (Boolean,Boolean) = (unionExpr(r1),unionExpr(r2))

       private def starExpr(r : RegEx) : Boolean = r.contains('*')

} // object GNFA

class GNFA(){

      private val DEBUG    = false

      private var states   = Set[State]()
      private var alphabet = Set[Symbl]()
      private var delta    = Map[(State,State),RegEx]()
      private var start    = "S"
      private var accept   = "A"
      private var name     = "_GNFA"

      def this(m : DFA) =
      {
	      this()

	      if (DEBUG) println(s"Creating a GNFA from ${m.getName()}")

	      val oldStates   = m.getStates()
	      val oldDelta    = m.getDelta()
	      val oldStart    = m.getStartState()
	      val oldAccept   = m.getAcceptStates()
	      val oldAlphabet = m.getAlphabet()

	      //::::::::::::::::::::::::::::::::::::::::::::::::::::::::::://
	      /*		Make the new alphabet and name		   */
	      //::::::::::::::::::::::::::::::::::::::::::::::::::::::::::://

      	      alphabet ++= ( oldAlphabet ++ Set(epsilon) )
	      name = m.getName() + "_GNFA"

	      //::::::::::::::::::::::::::::::::::::::::::::::::::::::::::://
	      /*	Make the new startState and acceptState unique	   */
	      //::::::::::::::::::::::::::::::::::::::::::::::::::::::::::://

	      while( oldStates contains start  ) start  = start  + p
	      while( oldStates contains accept ) accept = accept + p

	      if (DEBUG) {
	      	 println(s"new start: $start")
		 println(s"new accept: $accept")
	      } // DEBUG

	      //::::::::::::::::::::::::::::::::::::::::::::::::::::::::::://
	      /*	        Make the new set of States		   */
	      //::::::::::::::::::::::::::::::::::::::::::::::::::::::::::://

	      states ++= ( (oldStates--Set(NullState)) ++ Set(start,accept)  )

	      //::::::::::::::::::::::::::::::::::::::::::::::::::::::::::://
	      /*	Make the new delta function from the old one	   */
	      //::::::::::::::::::::::::::::::::::::::::::::::::::::::::::://

	      for ( state1 <- states ; state2 <- states) delta += ( (state1,state2) -> NullRegEx )
	      for ( input <- oldDelta ){

	      	  if (DEBUG) println(s"Working on input from old delta: $input")

		  val oldFrom  = input._1._1
		  val regEx    = input._1._2
		  val oldTo    = input._2
		  val newInput = (oldFrom,oldTo)

		  if( DEBUG ) println(s"newInput: $newInput")

		  if( !(oldTo.equals(NullState) || oldFrom.equals(NullState)) ) delta += (newInput -> GNFA.regExUnion(regEx,delta(newInput)))

		  if (DEBUG) println(s"after input, delta: $delta")

	      } // for input

	      for ( qi <- (states -- Set(start,accept)) ; qj <- (states -- Set(start,accept)) ){
	      	  if ( !(delta contains (qi,qj)) ) delta += ( (qi,qj) -> NullRegEx )
	      } // for

	      //::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::://
	      /*	Handle the new transitions from the new start and to the new accept	   */
	      //::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::://

	      for ( state <- (states--Set(start)) ) {
	      	  val newTrans = if ( state.equals(oldStart) ) epsilon else NullRegEx
		  delta += ((start,state) -> newTrans)
	      } // for

	      for ( state <- oldAccept ) delta += ( (state,accept) -> epsilon)

	      if (DEBUG) println("GNFA completed.")
      } // constructor from machine

      def this(m:NFA) = this(m.DFAify())

      def this(states : Set[State], alphabet : Set[Symbl], delta : Map[(State,State),RegEx], start : State, accept : State, name : String){
      	  this()
	  this.states   = states
	  this.alphabet = alphabet
	  this.delta    = delta
	  this.start    = start
	  this.accept   = accept
	  this.name     = name
      } // constructor

      def getStates()   : Set[State]               = Set[State]() ++ states

      def getAlphabet() : Set[Symbl] 		   = Set[Symbl]() ++ alphabet

      def getDelta()    : Map[(State,State),RegEx] = Map[(State,State),RegEx]() ++ delta

      def getStart()    : State 		   = start

      def getAccept()   : State 		   = accept

      def getName()     : String 		   = name

      override def toString() : String =
      {
	var ret = s"$name \nStart: $start \naccept: $accept\n"
	for ( (k,v) <- delta if !(v.equals(NullRegEx)) ) ret = ret + s"$k -> $v\n"
	ret
      }


} // GNFA

object GNFAtester extends App
{

       def mapFromSet( set : Set[((State,Symbl),State)] ) : Map[(State,Symbl),State] = {
       	   val map = Map[(State,Symbl),State]()
       	   for ( input <- set ) map += (input._1 -> input._2)
	   map
       } // mapFromSet

       val states1 = Set("0","1")										//All even length strings
       val sigma1  = Set("0","1")
       val delta1  = mapFromSet(Set( (("0","0"),"1"),(("0","1"),"1"),(("1","0"),"0"),(("1","1"),"0") ))
       val start1  = "0"
       val accept1 = Set("0")

       val states2 = Set("0","1")										//Even number of 1s
       val sigma2  = Set("0","1")
       val delta2  = mapFromSet(Set( (("0","0"),"0"),(("0","1"),"1"),(("1","0"),"1"),(("1","1"),"0") ))
       val start2  = "0"
       val accept2 = Set("0")

       val states3 = Set("0","1")										//Even number of 0s
       val sigma3  = Set("0","1")
       val delta3  = mapFromSet(Set( (("0","0"),"1"),(("0","1"),"0"),(("1","0"),"0"),(("1","1"),"1") ))
       val start3  = "0"
       val accept3 = Set("0")

       val states4 = Set("0","1")										//Odd number of 0s
       val sigma4  = Set("0","1")
       val delta4  = mapFromSet(Set( (("0","0"),"1"),(("0","1"),"0"),(("1","0"),"0"),(("1","1"),"1") ))
       val start4  = "0"
       val accept4 = Set("1")

       val states5 = Set("0","1")										//Empty language
       val sigma5  = Set("0","1")
       val delta5  = mapFromSet(Set( (("0","0"),"1"),(("0","1"),"0"),(("1","0"),"0"),(("1","1"),"1") ))
       val start5  = "0"
       val accept5 = Set("")

       val states6 = Set("0","1","2","3")									//Substring 001
       val sigma6  = Set("0","1")
       val delta6  = mapFromSet(Set( (("0","0"),"1"),(("0","1"),"0"),(("1","0"),"2"), (("1","1"),"0"),
       	   	     	  (("2","1"),"3") ,(("2","0"),"2") ,(("3","1"),"3"),(("3","0"),"3")))
       val start6  = "0"
       val accept6 = Set("3")

       val states7 = Set("00","01","10","11")										//Even 0's AND odd 1's
       val sigma7  = Set("0","1")
       val delta7  = mapFromSet(Set( (("00","0"),"10"),(("00","1"),"01"),(("10","0"),"00"),(("10","1"),"11"),
       	   	     	  (("11","1"),"10"),(("11","0"),"01"),(("01","1"),"00"),(("01","0"),"11")  ))
       val start7  = "00"
       val accept7 = Set("01")

       val states8 = Set("00","01","10","11")										//Even 0's OR odd 1's
       val sigma8  = Set("0","1")
       val delta8  = mapFromSet(Set( (("00","0"),"10"),(("00","1"),"01"),(("10","0"),"00"),(("10","1"),"11"),
       	   	     	  (("11","1"),"10"),(("11","0"),"01"),(("01","1"),"00"),(("01","0"),"11")  ))
       val start8  = "00"
       val accept8 = Set("00","01","11")

       val states9 = Set("00","01","10","11")										//Even 0's AND even 1's
       val sigma9  = Set("0","1")
       val delta9  = mapFromSet(Set( (("00","0"),"10"),(("00","1"),"01"),(("10","0"),"00"),(("10","1"),"11"),
       	   	     	  (("11","1"),"10"),(("11","0"),"01"),(("01","1"),"00"),(("01","0"),"11")  ))
       val start9  = "00"
       val accept9 = Set("00")

       val states10 = Set("00","01","10","11")										//Even 0's OR even 1's
       val sigma10  = Set("0","1")
       val delta10  = mapFromSet(Set( (("00","0"),"10"),(("00","1"),"01"),(("10","0"),"00"),(("10","1"),"11"),
       	   	     	  (("11","1"),"10"),(("11","0"),"01"),(("01","1"),"00"),(("01","0"),"11")  ))
       val start10  = "00"
       val accept10 = Set("00","01","10")

       val states11 = Set("00","01","10","11")										//odd 0's AND odd 1's
       val sigma11  = Set("0","1")
       val delta11  = mapFromSet(Set( (("00","0"),"10"),(("00","1"),"01"),(("10","0"),"00"),(("10","1"),"11"),
       	   	     	  (("11","1"),"10"),(("11","0"),"01"),(("01","1"),"00"),(("01","0"),"11")  ))
       val start11  = "00"
       val accept11 = Set("11")

       val states12 = Set("00","01","10","11")										//odd 0's OR odd 1's
       val sigma12  = Set("0","1")
       val delta12  = mapFromSet(Set( (("00","0"),"10"),(("00","1"),"01"),(("10","0"),"00"),(("10","1"),"11"),
       	   	     	  (("11","1"),"10"),(("11","0"),"01"),(("01","1"),"00"),(("01","0"),"11")  ))
       val start12  = "00"
       val accept12 = Set("10","01","11")

       val states13 = Set("0","1")										//Odd number of 1s
       val sigma13  = Set("0","1")
       val delta13  = mapFromSet(Set( (("0","0"),"0"),(("0","1"),"1"),(("1","0"),"1"),(("1","1"),"0") ))
       val start13  = "0"
       val accept13 = Set("1")

       val states14 = Set("0","1","2","3")									//w/o Substring 001
       val sigma14  = Set("0","1")
       val delta14  = mapFromSet(Set( (("0","0"),"1"),(("0","1"),"0"),(("1","0"),"2"), (("1","1"),"0"),
       	   	     	  (("2","1"),"3") ,(("2","0"),"2") ,(("3","1"),"3"),(("3","0"),"3")))
       val start14  = "0"
       val accept14 = Set("0","1","2")

       val states15 = Set("00","01","10","11")										//odd 0's AND even 1's
       val sigma15  = Set("0","1")
       val delta15  = mapFromSet(Set( (("00","0"),"10"),(("00","1"),"01"),(("10","0"),"00"),(("10","1"),"11"),
       	   	     	  (("11","1"),"10"),(("11","0"),"01"),(("01","1"),"00"),(("01","0"),"11")  ))
       val start15  = "00"
       val accept15 = Set("10")

       val states16 = Set("00","01","10","11")										//odd 0's OR even 1's
       val sigma16  = Set("0","1")
       val delta16  = mapFromSet(Set( (("00","0"),"10"),(("00","1"),"01"),(("10","0"),"00"),(("10","1"),"11"),
       	   	     	  (("11","1"),"10"),(("11","0"),"01"),(("01","1"),"00"),(("01","0"),"11")  ))
       val start16  = "00"
       val accept16 = Set("10","00","11")


       val m1  = new DFA(states1,sigma1,delta1,start1,accept1,"M1")				// M1 accepts all even length strings
       val m2  = new DFA(states2,sigma2,delta2,start2,accept2,"M2")				// M2 accepts all strings with even 1s
       val m3  = new DFA(states3,sigma3,delta3,start3,accept3,"M3")				// M3 accepts all strings with even 0s
       val m4  = new DFA(states4,sigma4,delta4,start4,accept4,"M4")				// M4 accepts strings with odd 0s
       val m5  = new DFA(states5,sigma5,delta5,start5,accept5,"M5")				// M5 accepts no strings
       val m6  = new DFA(states6,sigma6,delta6,start6,accept6,"M6")				// M6 accepts all strings with substring 001
       val m7  = new DFA(states7,sigma7,delta7,start7,accept7,"M7")				// M7 accepts all strings with even 0s and odd 1s
       val m8  = new DFA(states8,sigma8,delta8,start8,accept8,"M8")				// M8 accepts all strings with even 0s or odd 1s
       val m9  = new DFA(states9,sigma9,delta9,start9,accept9,"M9")				// M9 accepts all strings with even 0s and even 1s
       val m10 = new DFA(states10,sigma10,delta10,start10,accept10,"M10")				// M10 accepts all strings with even 0s or even 1s
       val m11 = new DFA(states11,sigma11,delta11,start11,accept11,"M11")				// M11 accepts all strings with odd 0s and odd 1s
       val m12 = new DFA(states12,sigma12,delta12,start12,accept12,"M12")				// M12 accepts all strings with odd 0s or odd 1s
       val m13 = new DFA(states13,sigma13,delta13,start13,accept13,"M13")				// M13 accepts all strings with odd 1s
       val m14 = new DFA(states14,sigma14,delta14,start14,accept14,"M14")				// M14 accepts all strings without 001 as a substring
       val m15 = new DFA(states15,sigma15,delta15,start15,accept15,"M15")				// M15 accepts all strings with odd 0s and even 1s
       val m16 = new DFA(states16,sigma16,delta16,start16,accept16,"M16")				// M16 accepts all strings with odd 0s or even 1s

       val m17 = m2.intersect(m3)
       val m18 = m2.union(m3)
       val m19 = m2.intersect(m4)
       val m20 = m2.union(m4)
       val m21 = m3.intersect(m13)
       val m22 = m3.union(m13)
       val m23 = m4.intersect(m13)
       val m24 = m4.union(m13)
       val m25 = m2.complement()
       val m26 = m3.complement()
       val m27 = m6.complement()
       val m28 = m4.complement()
       val m29 = m7.complement()
       val m30 = m8.complement()
       val m31 = m9.complement()
       val m32 = m10.complement()
       val m33 = m11.complement()
       val m34 = m12.complement()
       val m35 = m13.complement()
       val m36 = m14.complement()
       val m37 = m15.complement()
       val m38 = m16.complement()

       val langs = Array.ofDim[String](13)

       val machines = Array.ofDim[DFA](13)

       for ( i <- 0 until 13 ) {
       	   i +1  match {
	     case 1  => machines(i) = m1
	     case 2  => machines(i) = m2
	     case 3  => machines(i) = m3
	     case 4  => machines(i) = m4
	     case 5  => machines(i) = m5
	     case 6  => machines(i) = m6
	     case 7  => machines(i) = m7
	     case 8  => machines(i) = m8
	     case 9  => machines(i) = m9
	     case 10 => machines(i) = m10
	     case 11 => machines(i) = m11
	     case 12 => machines(i) = m12
	     case 13 => machines(i) = m13
	   } // match
       } // for

       val RegExs = Array.ofDim[RegEx](13)

       for ( i <- 0 to 12 ){
       	   i+1 match{
	       case 1 => langs(i) = "Even length strings"
	       case 2 => langs(i) = "even 1s"
	       case 3 => langs(i) = "even 0s"
	       case 4 => langs(i) = "odd 1s"
	       case 5 => langs(i) = "no strings"
	       case 6 => langs(i) = "all strings with the substring 001"
	       case 7 => langs(i) = "all strings with even 0s and odd 1s"
	       case 8 => langs(i) = "even 0s or odd 1s"
	       case 9 => langs(i) = "even 0s and even 1s"
	       case 10 => langs(i) = "all strings with even 0s or even 1s"
	       case 11 => langs(i) = "odd 0s and odd 1s"
	       case 12 => langs(i) = "odd os or odd 1s"
	       case 13 => langs(i) = "odd 1s"
	   } // match
       } // for

       for ( i <- 0 until 13 ) {
       	   i +1  match {
	     case 1  => RegExs(i)=GNFA.convert(machines(i))
	     case 2  => RegExs(i)=GNFA.convert(machines(i))
	     case 3  => RegExs(i)=GNFA.convert(machines(i))
	     case 4  => RegExs(i)=GNFA.convert(machines(i))
	     case 5  => RegExs(i)=GNFA.convert(machines(i))
	     case 6  => RegExs(i)=GNFA.convert(machines(i))
	     case 7  => RegExs(i)=GNFA.convert(machines(i))
	     case 8  => RegExs(i)=GNFA.convert(machines(i))
	     case 9  => RegExs(i)=GNFA.convert(machines(i))
	     case 10 => RegExs(i)=GNFA.convert(machines(i))
	     case 11 => RegExs(i)=GNFA.convert(machines(i))
	     case 12 => RegExs(i)=GNFA.convert(machines(i))
	     case 13 => RegExs(i)=GNFA.convert(machines(i))
	   } // match
       } // case

       for ( i <- 0 until 13 ) println(s"RegExs($i) : ${RegExs(i)} , Match: ${langs(i)}\n")
} // GNFA tester
/*
object smallGNFAtester extends App
{
       val states6 = Set("0","1","2","3")									//Substring 001
       val sigma6  = Set("0","1")
       val delta6  = Set( (("0","0"),"1"),(("0","1"),"0"),(("1","0"),"2"), (("1","1"),"0"),
       	   	     	  (("2","1"),"3") ,(("2","0"),"2") ,(("3","1"),"3"),(("3","0"),"3"))
       val start6  = "0"
       val accept6 = Set("3")

       val m6  = new DFA(states6,sigma6,delta6,start6,accept6,"M6")

       val gnfa6 = new GNFA(m6)

       //println(s"gnfa6: \n$gnfa6")
       val r6 = GNFA.convert(m6)
       println(s"R6: $r6)")
}*/
