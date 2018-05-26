//::::::::::::::::::::::::::::::::::::::::::::::
/** Author: Nick Klepp
 *  Date: June 6, 2017
 *  The DFA object represents a Deterministic Finite Automaton
 */
//::::::::::::::::::::::::::::::::::::::::::::::

package theory

import scala.collection.mutable.{Set,Map,Stack,ArrayBuffer}
import util.control.Breaks._
import TypeDefs._

class DFA() extends FiniteAutomaton
{

    //:::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
    /** Private instance variables which define a DFA
     *  states   : the set of states
     *  alphabet : the alphabet for the input strings
     *  delta    : the transition function, delta : States X Alphabet -> States
     *  start    : the start state, see also q_0
     *  accept 	 : the set of accept states
     *  name	 : the name of the machine
     */
    //:::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::

    private val DEBUG    = false
    private val DEBUGG   = true
    private val DEBUGGG  = false
    //::::::::::::::::::::::::::::::::::::::::::::::::::::::::::://
    /*		The private instance variables		   */		// TODO : make start and name a val
    //::::::::::::::::::::::::::::::::::::::::::::::::::::::::::://
    private val states   = Set[State]()
    private val alphabet = Set[Symbl]()
    private val delta    = Map[(State,Symbl),State]()
    private var start    = ""
    private val accept   = Set[State]()
    private var name 	   = "M"
    private var valid    = true
    private var state    = start

    def this( states   : Set[State],
              alphabet : Set[Symbl],
              delta    : Map[(State,Symbl),State],
              start    : State,
              accept   : Set[State])
    {
  	  this()
  	  if (DEBUG) println(s"Making new machine: $name")
    	this.states   ++= states
  	  this.alphabet ++= alphabet
  	  setDelta( delta )
  	  setStart( start )
  	  setAccept( accept )
  	  this.state = start
  	  if (DEBUG) println(s"new machine ${toString()}")
    } // this

    def this( states   : Set[State],
              alphabet : Set[Symbl],
              delta    : Map[(State,Symbl),State],
              start    : State,
              accept   : Set[State],
              name     : String )
    {
      this()
      if (DEBUG) println(s"Making new machine: $name")
      this.states   ++= states
      this.alphabet ++= alphabet
      setDelta( delta )
      setStart( start )
      setAccept( accept )
      this.state = start
      this.name = name
      if (DEBUG) println(s"new machine ${toString()}")
    } // this

    /**********************************************************
     * The Mutator methods for the private instance variables *
     **********************************************************/

    private def setDelta(delta : Map[(State,Symbl),State]) = // : Map[(State,Symbl),State] =
    {
      for ( transition <- delta if validTransition(transition) )  {
        this.delta += (transition._1 -> transition._2)
	    } // for transition

	    for ( symbl <- alphabet ) {								//Fill out the unspecified transitions.
	        for ( state <- states ) {
	    	    val input = (state,symbl)
	    	    if ( !( delta contains input) ) {
              this.states += NullState
              this.delta += input -> NullState
            }
	        } // for state
	    } // for symbl
    } // setDelta

    private def setStart( start : State ){
      if ( states contains start ) this.start = start
	    else {
	    	 println(s"Invalid start state for $name : $start")
		     valid = false
	    } // else
    } // setStart()

    private def setAccept(accept : Set[State]) {
    	if ( (accept -- this.states).size == 0 ) {
	       this.accept ++= accept
	    } // if
	    else {
        for ( state <- accept if ( !((this.states contains state) || accept.size==0) ) ) {
          println(s"Invalid accept state for $name : |$state|")
        }
		    valid = false
	    } // else
    } // setAccept

    //:::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
    // The Accessor methods for the private instance variables
    //:::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::

    def getStates() = Set[State]() ++ states

    def getAlphabet() = Set[Symbl]() ++ alphabet

    def getDelta() = Map[(State,Symbl),State]() ++ delta

    def getAcceptStates() = Set[State]() ++ accept

    def getStartState() = start

    def getName() = name

    def isValid() = valid

    //:::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
    // Additional public methods for the class DFA
    //:::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::

    def compute(string: String) : Boolean =
    {
      for ( s <- string ) {
	       val input = (state,s.toString)
	       state = delta(input)
	    } // for
	    val finalState = state
	    state = start
	    return accept contains finalState
    } // compute

    def compute_record(string: String) : (Boolean,ArrayBuffer[State]) =
    {
      val history = ArrayBuffer(start)
      for ( s <- string ) {
	       val input = (state,s.toString)
	       state = delta(input)
         history += state
	    } // for
	    val finalState = state
	    state = start
      return ((accept contains finalState),history)
    }

    def complement() : DFA =
    {
    	val accept = states -- this.accept
      new DFA(states,alphabet,delta,start,accept,this.name+"_COMP")
    }

    def union(m2 : DFA) : DFA =
    {
      val states = Set[State]()

	    val delta1 = this.delta
	    val delta2 = m2.delta
	    val delta  = Map[(State,Symbl),State]()

	    val accept1 = this.getAcceptStates()
	    val accept2 = m2.getAcceptStates()
      val accept  = Set[State]()

	    val start1 = this.getStartState()
	    val start2 = m2.getStartState()
	    val start  = s"(${start1},${start2})"

	    val name1 = this.getName()
	    val name2 = m2.getName()
	    val name  = name1+"_UNION_"+name2

      val unchecked = Stack((start1,start2))
      states += start

      while( ! unchecked.isEmpty ) {
        val (check1,check2) = unchecked.pop()
        val newFrom = s"(${check1},${check2})"
        if ( (accept1 contains check1) || (accept2 contains check2)){
          accept += newFrom
        }
        for ( symbl <- alphabet ) {
          val (new1,new2) = (delta1(check1,symbl),delta2(check2,symbl))
          val newInput = (newFrom,symbl)
          val newTo = s"(${new1},${new2})"
          delta += (newInput -> newTo)
          if ( !(states contains newTo) ){
              states += newTo
              unchecked.push((new1,new2))
          } // if
        } //  for symbol
      } // while

	    new DFA(states, alphabet, delta, start, accept, name)
    } // union

    def intersect(m : DFA) : DFA =
    {
	    val m2 : DFA = m.DFAify()
	    if (DEBUG) println(s"intersecting $toString \nand ${m2.toString}")

	    val states = Set[State]()

	    val start1 = this.getStartState()
	    val start2 = m2.getStartState()
	    val start  = s"(${start1},${start2})"

	    val delta1 = this.delta // this.map
	    val delta2 = m2.delta // m2.map
	    val delta  = Map[(State,Symbl),State]() // Set[((State,Symbl),State)]()

	    val accept1 = this.getAcceptStates()
	    val accept2 = m2.getAcceptStates()
	    val accept  = Set[State]()

	    val name1 = this.getName()
	    val name2 = m2.getName()
	    val name  = name1+"_INTERSECT_"+name2

      val unchecked = Stack((start1,start2))

      states += start

      while( ! unchecked.isEmpty ) {
        val (check1,check2) = unchecked.pop()
        val newFrom = s"(${check1},${check2})"
        if ( (accept1 contains check1) && (accept2 contains check2) ){
          accept += newFrom
        } // if
        for ( symbl <- alphabet ) {
          val (new1,new2) = (delta1(check1,symbl),delta2(check2,symbl))
          val newInput = (newFrom,symbl)
          val newTo = s"(${new1},${new2})"
          delta += (newInput -> newTo)
          if ( !(states contains newTo) ) {
            unchecked.push((new1,new2))
            states += newTo
          } // if
        } //  for symbol
      } // while
	    new DFA(states, alphabet, delta, start, accept, name)
    } // intersect

    def kleeneStar() = NFAify().kleeneStar().DFAify()

    def NFAify()  =
    {
      val newDelta = Map[(State,Symbl),Set[State]]()
	    for ( d <- delta ) newDelta += d._1 -> Set(d._2)
	    new NFA(states,alphabet,newDelta,start,accept,s"${name}_NFA")
    }

    def recognizesEmptyLanguage() : Boolean =
    {
      val reachable = Set[State]()
	    reachable += start
	    val toTest    = reachable.clone
	    while( toTest.size != 0 ){
	        val testClone = toTest.clone
	        for( symbl <- alphabet ){
	        	 for ( state <- testClone ){
	    	         toTest -= state						// w/o creating a clone of toTest, would this mess up the iterator?
	        	     val newState = delta(state,symbl)
	    	          if( !(reachable contains newState) ){
	    	     	        toTest += newState					// would this, more importatly?
	    		            reachable += newState
	    	          } // if
	        	 }// for state
	        } // for symbl
	    } // while
	    return (accept intersect reachable).size == 0
    } // empty

    def equals(m2: DFA) : Boolean =
    {

      val m1Comp = complement()
	    val m2Comp = m2.complement()
	    val mm1	   = intersect(m2Comp)
	    val mm2    = m2.intersect(m1Comp)
	    val mm	   = mm1.union(mm2)

	    return mm.recognizesEmptyLanguage()
    }

    def equals(m2 : NFA) : Boolean = equals(m2.DFAify())

    def minimize() : DFA =
    {
      if (DEBUGG) println(s"Minimizing : \n${this}")
      //Reduce the machine to its reachable states
      val rreachable = reachable()
      if (DEBUGG) println(s"rreachable: \n${rreachable}")
      //Differentiate the reachable states
      val (differentiated,stateFromInt) = rreachable.differentiate()
      if (DEBUGG) {
        println(s"differentiated: \n${differentiated.deep}")
        println(s"stateFromInt: \n${stateFromInt}")
      }
      //Merge states which aren't differntiable
      val merge_sets = merge_states(differentiated,stateFromInt)
      if (DEBUGG) println(s"merge_sets: \n${merge_sets}")
      //Get the set of states and their associations with the merge_sets
      val (states, associate) = associate_merge_sets(merge_sets)
      //set up the remaining data structures to return the new minimal machine
      if (DEBUGG) println(s"states: \n${states}\nassociate: \n${associate}")

      val delta  = Map[(State,Symbl),State]()
      val accept = Set[State]()
      val start  = getNewState(this.start,associate)

      //Now we populate the above data structures
      for (state <- this.states){
        if(DEBUGG) println(s"state: \n${state}")
        //Find the new "merge state" this state is associated with
        val newState = getNewState(state,associate)
        if(DEBUGG) println(s"newState: ${newState}")
        //We only need to work if we haven't handled the merge state yet
        if ( delta.
             keys.
             map(x => x._1).
             filter(x => x == newState).
             toList.
             length == 0 ){
          for (a <- alphabet){
             //Use the old transition function to update the new one
             if (DEBUGG) println(s"this.delta_THREE: \n${this.delta}")
             val sstate = this.delta((state,a))
             val nnewState = getNewState(sstate,associate)
             delta += (newState,a)->nnewState
             //handle new accept states
             if (this.accept contains state) accept += newState
          } // for a
        } // if
      } // for state
      //new DFA(states, alphabet, delta, start, accept, name)
      return new DFA(states,alphabet,delta,start,accept,name+"_MIN")
    } // minimize

    override def toString() : String =
    {
	     s"${this.name}\n"                   +
	     s"Start: $start\n"                  +
	     s"Accept: ${setToString(accept)}\n" +
	     s"Delta: \n$deltaString"
    }

    def DFAify() = this

    //:::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
    // Additional private methods for the class DFA
    //:::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
    private def associate_merge_sets(merge_sets : Set[Set[State]]) :
                                            (Set[State],Map[Set[State],State]) =
    {
      val states    = Set[State]()
      val associate = Map[Set[State],State]()
      //Create new states and add it to the new set of states from the merge sets
      for (set <- merge_sets){
        val q = set.mkString("_")
        states += q
        associate += set -> q
      } // for set

      return (states,associate)
    }

    private def getNewState(state     : State,
                            associate : Map[Set[State],State]) : State =
    {
      var ret = ""
      breakable{for (set <- associate.keys){
        if (set contains state){
           ret = associate(set)
           break
        }
      }} // for
      return ret
    } // getNewState

    private def merge_states(differentiated : Array[Array[Boolean]],
                             stateFromInt   : Map[Int,State]) : Set[Set[State]] =
    {
      val merge_sets = Set[Set[State]]()
      val unmerged = states.clone
      for (i <- 0 until differentiated.length-1){
        for (j <- i+1 until differentiated(i).length){
          if (! differentiated(i)(j) ){
            val si = stateFromInt(i)
            val sj = stateFromInt(j)
            unmerged -= si
            unmerged -= sj
            breakable{for ( set <- merge_sets ){
              if ( (set contains si) || (set contains sj) ){
                set += si
                set += sj
                break
              } // if
            }} // For
            // if we get here then there wasn't a merge set with either si or sj
            merge_sets += Set(si,sj)
          } // if
        } // for i
      } // for j
      //We'll add the singleton sets for any states that weren't part of a merge
      for ( s <- unmerged ) merge_sets += Set(s)
      return merge_sets
    } // merge_states

    private def differentiate() : (Array[Array[Boolean]],Map[Int,State]) =
    {
      val last_index = states.size - 1
      //differentiate the accept from the non-accept states
      val (differentiated,
           stateFromInt  ,
           intFromState  ,
           dependent ) = init_differentiate()

      if (DEBUGG) {
        println("After init_differentiate")
        println(s"differentiated: \n${differentiated.deep}")
        println(s"stateFromInt: \n${stateFromInt}")
        println(s"intFromState: \n${intFromState}")
        println(s"last_index: ${last_index}")
      } // if DEBUGG
      //Differentiate everything else possible
      for ( i <- 0 until last_index){
        for (j <- i+1 to last_index){
          if (DEBUGG) println(s"Checking differentation for ($i,$j)")
          //We only need to try to differentiate a cell if it's not yet differentiated
          if (! (differentiated(i)(j))){
            val s1 = stateFromInt(i)
            val s2 = stateFromInt(j)
            //We'll use this to populate the dependent table later
            val future = Set[(Int,Int)]()
            //Check to see if the two states are differentiated by any character
            breakable{for ( a <- alphabet ) {
              val r1 = delta((s1,a))
              val r2 = delta((s2,a))
              if (DEBUGG){
                 println(s"Checking $a for differentiating ($i,$j)")
                 println(s"$a led to ${r1},${r2}")
              }
              /*
              The states are definitely not differentiated by this symbol if they
              each transition to the same state or if they each transition back to
              themvselves (or a mirror image of themselves)
              */
              if ( (r1 != r2) && ( Set(r1,r2) != Set(s1,s2) ) ) {
                val rr1 = if (intFromState(r2)>intFromState(r1)) intFromState(r1)
                          else intFromState(r2)
                val rr2 = if (rr1 == intFromState(r1)) intFromState(r2)
                          else intFromState(r1)
                if (DEBUGG) {
                  println(s"Need to check differentiation:\nr's: \n${Set(r1,r2)},\ns's: \n${Set(s1,s2)}")
                  println(s"rr1: ${rr1}, rr2: ${rr2}")
                  println(s"differentiated(${rr1})(${rr2}): ${differentiated(rr1)(rr2)}")
                }
                if (differentiated(rr1)(rr2)) {
                  if (DEBUGG) println(s"differentiating $i,$j")
                  differentiate2(i,j,differentiated,dependent)
                  break
                } // if
                else future += ( (rr1,rr2) )
              } // if
            } // for a
            for ( (p1,p2) <- future ) {
              dependent(p1)(p2)  += ( (i,j) )
              if (DEBUGG) println(s"Updated dependent($p1)($p2): ${dependent(p1)(p2)}")
            }
            if (DEBUGG) println(s"After updating dependent: ${dependent.deep}")
          } // if
        } // for j
      } // for i
      } // breakable
      return (differentiated,stateFromInt)
    } // differentiate

    private def init_differentiate() : (Array[Array [Boolean]],
                                        Map[Int, State],
                                        Map[State, Int],
                                        Array[Array[Set[(Int,Int)]]]
                                       ) =
    {
      val dependent = Array.ofDim[Set[(Int,Int)]](states.size,states.size)
      //initialize the dependent array
      for (i <- 0 until states.size){
        for (j <- 0 until states.size){
          dependent(i)(j) = Set[(Int,Int)]()
        }
      }
      val differentiated = Array.ofDim[Boolean](states.size,states.size)
      //We'll use these to reference from states to indices and vice versa
      val stateFromInt = states.
                         toList.
                         zipWithIndex.
                         map( x => (x._2,x._1) ).
                         toMap

      val intFromState = states.
                         toList.
                         zipWithIndex.
                         toMap
      //This makes mutable maps from the immutable ones above
      val sstateFromInt = Map(stateFromInt.toSeq: _*)
      val iintFromState = Map(intFromState.toSeq: _*)

      if (DEBUGG){
        println("in init_differentiate")
        println(s"stateFromInt: \n${stateFromInt}")
        println(s"intFromState: \n${intFromState}")
        println(s"sstateFromInt: \n${sstateFromInt}")
        println(s"iintFromState: \n${iintFromState}")
      }
      val last_index = differentiated.length - 1
      for (i <- 0 until last_index){
        for (j <- i+1 to last_index){
          val s1 = stateFromInt(i)
          val s2 = stateFromInt(j)
          if ( init_diff_helper(s1,s2) ) differentiated(i)(j) = true
        } // for j
      } // for i
      return (differentiated, sstateFromInt, iintFromState, dependent)
    } // init_differentiate

    private def init_diff_helper(s1 : State , s2 : State) : Boolean =
    {
      val one = (this.accept contains s1) && !(this.accept contains s2)
      val two = (this.accept contains s2) && !(this.accept contains s1)
      return one || two
    } // init_diff_helper

    private def differentiate2(
                       i              : Int,
                       j              : Int,
                       differentiated : Array[Array[Boolean]],
                       dependent      : Array[Array[Set[(Int,Int)]]]) : Unit =
    {
      if (DEBUGG) {
        println(s"Differentiating $i,$j")
        println(s"dependent(i)(j): ${dependent(i)(j)}")
      }
      differentiated(i)(j) = true
      for ( (p1,p2) <- dependent(i)(j) ) {
        differentiate2(p1,p2,differentiated,dependent)
      } // for

    } // differentiate2

    private def reachable() : DFA =
    {

          val start = this.start

          val notChecked = Stack(start)
          val states     = Set[State]()
          val accept     = Set[State]()

          while ( ! (notChecked.isEmpty) ){
              val state = notChecked.pop()
              if (DEBUGG) (println(s"Found: ${state}"))
              states += state
              if (this.accept contains state) accept += state
              for (a <- this.alphabet){
                val newState = delta((state,a))
                if (DEBUGG) println(s"Might find: ${newState} because of ${a}")
                if (! (states contains newState) ){
                  notChecked.push(newState)
                  if (DEBUGG) println(s"Will find: ${newState}")
                } // if
              } // for
          } // while
          if(DEBUGG){
             println(s"states: \n${states}\nthis.states: \n${this.states}")
             println(s"states == this.states: ${states == this.states}")
          }
          if (states == this.states) return this
          else return new DFA(states,
                              alphabet,
                              this.delta.retain((k,v)=> states contains k._1),
                              start,
                              accept,
                              this.name + "_REACH")
    }
    private def validTransition( transition : ((State,Symbl),State) ) : Boolean =
    {
      if (DEBUG) println(s"validating transition: $transition")
	    return ( validFromState(transition)  &&
               validToState(transition)    &&
               validInputSymbl(transition) &&
               newInput(transition) )
    } // validTransition

    private def validFromState(transition : ((State,Symbl),State) ) : Boolean =
    {
      if (states contains transition._1._1) return true
	    else handleInvalid(1,transition)
    } // validFromState

    private def validToState(transition : ((State,Symbl),State)) : Boolean =
    {
      if (states contains transition._2) return true
	    else handleInvalid(2,transition)
    } // validToState

    private def validInputSymbl( transition : ((State,Symbl),State) ) : Boolean =
    {
      if (alphabet contains transition._1._2) return true
	    else handleInvalid(3,transition)
    }

    private def newInput( transition : ((State,Symbl),State))	: Boolean =
    {
    	if (delta contains transition._1 ) handleInvalid(4,transition)
	    else return true
    }

    private def handleInvalid(i : Int, transition : ((State,Symbl),State)) : Boolean =
    {
      val fromState  = transition._1._1
	    val inputSymbl = transition._1._2
	    val toState    = transition._2
      i match{
	       case 1 => {
	  	       println(s"Invalid transition: delta($fromState,$inputSymbl)->$toState)"+
                     s" :: $fromState not in the set of states for ${name}.")
		         valid = false
	       } // case 1
	       case 2 => {
	  	       println(s"Invalid transition: delta($fromState,$inputSymbl)->$toState)"+
                     s" :: $toState not in the set of states for ${name}.")
		         valid = false
	       } // case 2
	       case 3 => {
	    	     println(s"Invalid transition: delta($fromState,$inputSymbl)->$toState)"+
                     s" :: $inputSymbl not in the alphabet for ${name}.")
		         valid = false
	       } // case 3
	       case 4 => {
             println(s"Invalid transition: delta($fromState,$inputSymbl)->$toState)"+
                     s" :: transition already specified for input ${transition._1} for ${name}.")
	           valid = false
	       } // case 4
	    } // match
	    false
    } // handleInvalid

    def setToString(set : Set[String]) : String = if (set.size!=0) "{" + set.reduceLeft(_ + ";" +_) + "}" else "{}"

    def deltaString : String =
    {
      var str = ""
	    for ( (k,v) <- delta ) str = str + s"$k -> $v\n"
	    str
    } // deltaString

}// DFA

object DFATestMethods{
       def testAcceptance(m1 : DFA , s : String , expRes : Boolean){
       	   m1.compute(s) == expRes
       } // testAcceptance

       def testEquality(m1 : DFA , m2 : DFA , expRes : Boolean){
       	   m1.equals(m2) == expRes
       } // testEquality

       def testSuiteEquality(machines : Array[DFA], answers : Array[Array[Boolean]]){
       	   var pass = true
       	   for ( i <- 0 until answers.length ) {
	            for ( j <- i until answers.length ) {
	       	       val testRes = machines(i).equals(machines(j))
		             val expRes  = answers(i)(j)
		             val m1s     = machines(i).toString()
		             val m2s     = machines(j).toString()
	       	       if ( !(testRes == expRes) ){
		                 println(s"Test failed for equality. ${m1s}\n${m2s}\nExpected: ${expRes}\nObserved: ${testRes}")
		                 println(s"i: ${i+1}, j: ${j+1}")
		             } // if
	            } // for j
	            if (pass) println(s"Test suite equality passed for ${machines(i).getName()}")
	         } // for i
	         if (pass) println(s"testSuiteEqulity passed")
       } // testSuiteEqualitydef

       def testSuiteAcceptance(machine : DFA, strings : Array[String], answers : Array[Boolean]){
       	   var pass = true
       	   for ( i <- 0 until answers.length ) {
	       	   val string = strings(i)
	       	   val testRes = machine.compute(string)
		         val expRes  = answers(i)
		         val m1s     = machine.toString()
	       	   if ( !(testRes == expRes) ){
		             println(s"Test failed for acceptance. \nString: ${string}\nMachine: \n${m1s}Expected: ${expRes}\nObserved: ${testRes}\n\n")
		             pass = false
		         } // if
	         } // for
	         if (pass) println(s"Acceptance suite passed for ${machine.getName()}")
       } // testSuiteEquality

       def testSuitMinizeSoft(ar1 : Array[DFA], ar2 : Array[DFA]){
         var pass = true
         for (i <- 0 until ar1.length){
           if (! ar1(i).equals(ar2(i)) ){
             pass = false
             println(s"Test failed for minimization. \nm1: \n${ar1(i)}\nm2: \n${ar2(i)}")
           }
         } // for i
         if (pass) println(s"Soft test for minimization passed.")
       }
} // DFATestMethods

object DFATester extends App{

       import DFATestMethods._

       val DEBUG = false

       def mapFromSet( set : Set[((State,Symbl),State)] )
                                            : Map[(State,Symbl),State] =
       {
       	   val map = Map[(State,Symbl),State]()
       	   for ( input <- set ) map += (input._1 -> input._2)
	         map
       } // mapFromSet

       val states1 = Set("0","1")										//All even length strings
       val sigma1  = Set("0","1")
       val delta1  = mapFromSet(Set( (("0","0"),"1"),
                                     (("0","1"),"1"),
                                     (("1","0"),"0"),
                                     (("1","1"),"0") ))
       val start1  = "0"
       val accept1 = Set("0")

       val states2 = Set("0","1")										//Even number of 1s
       val sigma2  = Set("0","1")
       val delta2  = mapFromSet(Set( (("0","0"),"0"),
                                     (("0","1"),"1"),
                                     (("1","0"),"1"),
                                     (("1","1"),"0") ))
       val start2  = "0"
       val accept2 = Set("0")

       val states3 = Set("0","1")										//Even number of 0s
       val sigma3  = Set("0","1")
       val delta3  = mapFromSet(Set( (("0","0"),"1"),
                                     (("0","1"),"0"),
                                     (("1","0"),"0"),
                                     (("1","1"),"1") ))
       val start3  = "0"
       val accept3 = Set("0")

       val states4 = Set("0","1")										//Odd number of 0s
       val sigma4  = Set("0","1")
       val delta4  = mapFromSet(Set( (("0","0"),"1"),
                                     (("0","1"),"0"),
                                     (("1","0"),"0"),
                                     (("1","1"),"1") ))
       val start4  = "0"
       val accept4 = Set("1")

       val states5 = Set("0","1")										//Empty language
       val sigma5  = Set("0","1")
       val delta5  = mapFromSet(Set( (("0","0"),"1"),
                                     (("0","1"),"0"),
                                     (("1","0"),"0"),
                                     (("1","1"),"1") ))
       val start5  = "0"
       val accept5 = Set[State]()

       val states6 = Set("0","1","2","3")									//Substring 001
       val sigma6  = Set("0","1")
       val delta6  = mapFromSet(Set( (("0","0"),"1"),
                                     (("0","1"),"0"),
                                     (("1","0"),"2"),
                                     (("1","1"),"0"),
       	   	     	                   (("2","1"),"3"),
                                     (("2","0"),"2"),
                                     (("3","1"),"3"),
                                     (("3","0"),"3")))
       val start6  = "0"
       val accept6 = Set("3")

       val states7 = Set("00","01","10","11")										//Even 0's AND odd 1's
       val sigma7  = Set("0","1")
       val delta7  = mapFromSet(Set( (("00","0"),"10"),
                                     (("00","1"),"01"),
                                     (("10","0"),"00"),
                                     (("10","1"),"11"),
       	   	     	                   (("11","1"),"10"),
                                     (("11","0"),"01"),
                                     (("01","1"),"00"),
                                     (("01","0"),"11")  ))
       val start7  = "00"
       val accept7 = Set("01")

       val states8 = Set("00","01","10","11")										//Even 0's OR odd 1's
       val sigma8  = Set("0","1")
       val delta8  = mapFromSet(Set( (("00","0"),"10"),
                                     (("00","1"),"01"),
                                     (("10","0"),"00"),
                                     (("10","1"),"11"),
       	   	     	                   (("11","1"),"10"),
                                     (("11","0"),"01"),
                                     (("01","1"),"00"),
                                     (("01","0"),"11")  ))
       val start8  = "00"
       val accept8 = Set("00","01","11")

       val states9 = Set("00","01","10","11")										//Even 0's AND even 1's
       val sigma9  = Set("0","1")
       val delta9  = mapFromSet(Set( (("00","0"),"10"),
                                     (("00","1"),"01"),
                                     (("10","0"),"00"),
                                     (("10","1"),"11"),
       	   	     	                   (("11","1"),"10"),
                                     (("11","0"),"01"),
                                     (("01","1"),"00"),
                                     (("01","0"),"11")  ))
       val start9  = "00"
       val accept9 = Set("00")

       val states10 = Set("00","01","10","11")										//Even 0's OR even 1's
       val sigma10  = Set("0","1")
       val delta10  = mapFromSet(Set( (("00","0"),"10"),
                                      (("00","1"),"01"),
                                      (("10","0"),"00"),
                                      (("10","1"),"11"),
       	   	     	                    (("11","1"),"10"),
                                      (("11","0"),"01"),
                                      (("01","1"),"00"),
                                      (("01","0"),"11")  ))
       val start10  = "00"
       val accept10 = Set("00","01","10")

       val states11 = Set("00","01","10","11")										//odd 0's AND odd 1's
       val sigma11  = Set("0","1")
       val delta11  = mapFromSet(Set( (("00","0"),"10"),
                                      (("00","1"),"01"),
                                      (("10","0"),"00"),
                                      (("10","1"),"11"),
       	   	     	                    (("11","1"),"10"),
                                      (("11","0"),"01"),
                                      (("01","1"),"00"),
                                      (("01","0"),"11")))
       val start11  = "00"
       val accept11 = Set("11")

       val states12 = Set("00","01","10","11")										//odd 0's OR odd 1's
       val sigma12  = Set("0","1")
       val delta12  = mapFromSet(Set( (("00","0"),"10"),
                                      (("00","1"),"01"),
                                      (("10","0"),"00"),
                                      (("10","1"),"11"),
       	   	     	                    (("11","1"),"10"),
                                      (("11","0"),"01"),
                                      (("01","1"),"00"),
                                      (("01","0"),"11")  ))
       val start12  = "00"
       val accept12 = Set("10","01","11")

       val states13 = Set("0","1")										//Odd number of 1s
       val sigma13  = Set("0","1")
       val delta13  = mapFromSet(Set( (("0","0"),"0"),
                                      (("0","1"),"1"),
                                      (("1","0"),"1"),
                                      (("1","1"),"0") ))
       val start13  = "0"
       val accept13 = Set("1")

       val states14 = Set("0","1","2","3")									//w/o Substring 001
       val sigma14  = Set("0","1")
       val delta14  = mapFromSet(Set( (("0","0"),"1"),
                                      (("0","1"),"0"),
                                      (("1","0"),"2"),
                                      (("1","1"),"0"),
       	   	     	                    (("2","1"),"3"),
                                      (("2","0"),"2"),
                                      (("3","1"),"3"),
                                      (("3","0"),"3")))
       val start14  = "0"
       val accept14 = Set("0","1","2")

       val states15 = Set("00","01","10","11")										//odd 0's AND even 1's
       val sigma15  = Set("0","1")
       val delta15  = mapFromSet(Set( (("00","0"),"10"),
                                      (("00","1"),"01"),
                                      (("10","0"),"00"),
                                      (("10","1"),"11"),
       	   	     	                    (("11","1"),"10"),
                                      (("11","0"),"01"),
                                      (("01","1"),"00"),
                                      (("01","0"),"11")  ))
       val start15  = "00"
       val accept15 = Set("10")

       val states16 = Set("00","01","10","11")										//odd 0's OR even 1's
       val sigma16  = Set("0","1")
       val delta16  = mapFromSet(Set( (("00","0"),"10"),
                                      (("00","1"),"01"),
                                      (("10","0"),"00"),
                                      (("10","1"),"11"),
       	   	     	                    (("11","1"),"10"),
                                      (("11","0"),"01"),
                                      (("01","1"),"00"),
                                      (("01","0"),"11")  ))
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

       val m1_min = m1.minimize()
       val m2_min = m2.minimize()
       val m3_min = m3.minimize()
       val m4_min = m4.minimize()
       val m5_min = m5.minimize()
       val m6_min = m6.minimize()
       val m7_min = m7.minimize()
       val m8_min = m8.minimize()
       val m9_min = m9.minimize()
       val m10_min = m10.minimize()
       val m11_min = m11.minimize()
       val m12_min = m12.minimize()
       val m13_min = m13.minimize()
       val m14_min = m14.minimize()
       val m15_min = m15.minimize()
       val m16_min = m16.minimize()
       val m17_min = m17.minimize()
       val m18_min = m18.minimize()
       val m19_min = m19.minimize()
       val m20_min = m20.minimize()
       val m21_min = m21.minimize()
       val m22_min = m22.minimize()
       val m23_min = m23.minimize()
       val m24_min = m24.minimize()
       val m25_min = m25.minimize()
       val m26_min = m26.minimize()
       val m27_min = m27.minimize()
       val m28_min = m28.minimize()
       val m29_min = m29.minimize()
       val m30_min = m30.minimize()
       val m31_min = m31.minimize()
       val m32_min = m32.minimize()
       val m33_min = m33.minimize()
       val m34_min = m34.minimize()
       val m35_min = m35.minimize()
       val m36_min = m36.minimize()
       val m37_min = m37.minimize()
       val m38_min = m38.minimize()

       val strings = Array("","11111","111111","10101","101010","110011","001100","01100","10011")

       val a1 = Array(true,false,true,false,true,true,true,false,false)
       val a2 = Array(true,false,true,false,false,true,true,true,false)
       val a3 = Array(true,true,true,true,false,true,true,false,true)
       val a4 = Array(false,false,false,false,true,false,false,true,false)
       val a5 = Array(false,false,false,false,false,false,false,false,false)
       val a6 = Array(false,false,false,false,false,true,true,false,true)
       val a7 = Array(false,true,false,true,false,false,false,false,true)
       val a8 = Array(true,true,true,true,true,true,true,false,true)
       val a9 = Array(true,false,true,false,false,true,true,false,false)
       val a10 = Array(true,true,true,true,false,true,true,true,true)
       val a11 = Array(false,false,false,false,true,false,false,false,false)
       val a12 = Array(false,true,false,true,true,false,false,true,true)
       val a13 = Array(false,true,false,true,true,false,false,false,true)
       val a14 = Array(true,true,true,true,true,false,false,true,false)
       val a15 = Array(false,false,false,false,false,false,false,true,false)
       val a16 = Array(true,false,true,false,true,true,true,true,false)

       val a17 : Array[Boolean] = a9
       val a18 : Array[Boolean] = a10
       val a19 : Array[Boolean] = a15
       val a20 : Array[Boolean] = a16
       val a21 : Array[Boolean] = a7
       val a22 : Array[Boolean] = a8
       val a23 : Array[Boolean] = a11
       val a24 : Array[Boolean] = a12
       val a25 : Array[Boolean] = a13
       val a26 : Array[Boolean] = a4
       val a27 : Array[Boolean] = a14
       val a28 : Array[Boolean] = a3
       val a29 : Array[Boolean] = a16
       val a30 : Array[Boolean] = a15
       val a31 : Array[Boolean] = a12
       val a32 : Array[Boolean] = a11
       val a33 : Array[Boolean] = a10
       val a34 : Array[Boolean] = a9
       val a35 : Array[Boolean] = a2
       val a36 : Array[Boolean] = a6
       val a37 : Array[Boolean] = a8
       val a38 : Array[Boolean] = a7

       val machines : Array[DFA] = Array(m1 ,m2 ,m3 ,m4 ,m5 ,m6 ,m7 ,m8 ,m9 ,m10,
                                         m11,m12,m13,m14,m15,m16,m17,m18,m19,m20,
                                         m21,m22,m23,m24,m25,m26,m27,m28,m29,m30,
                                         m31,m32,m33,m34,m35,m36,m37,m38)
       val min_machines : Array[DFA] = Array(m1_min ,m2_min ,m3_min ,m4_min ,
                                             m5_min ,m6_min ,m7_min ,m8_min ,
                                             m9_min ,m10_min,m11_min,m12_min,
                                             m13_min,m14_min,m15_min,m16_min,
                                             m17_min,m18_min,m19_min,m20_min,
                                             m21_min,m22_min,m23_min,m24_min,
                                             m25_min,m26_min,m27_min,m28_min,
                                             m29_min,m30_min,m31_min,m32_min,
                                             m33_min,m34_min,m35_min,m36_min,
                                             m37_min,m38_min)
       val answers  = Array(a1 ,a2 ,a3 ,a4 ,a5 ,a6 ,a7 ,a8 ,a9 ,a10,a11,a12,a13,
                            a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24,a25,a26,
                            a27,a28,a29,a30,a31,a32,a33,a34,a35,a36,a37,a38)

       val answers2 = Array.ofDim[Array[Boolean]](38)
       if (DEBUG) println(s"answers2.size: ${answers2.length}")
       for ( i <- 0 to 37){
       	   if (DEBUG) println(s"i: $i")
       	   answers2(i) = Array.fill(38)(false)
	         if (DEBUG) println(s"answers2(i).length: ${answers2(i).length}")
       	   for ( j <- 0 to 37 ) {
	            if (DEBUG) println(s"j: $j")
	            if ( i == j ) answers2(i)(j) = true
	            else (i+1,j+1) match {
		               case (2,35) => answers2(i)(j) = true

		               case (3,28) => answers2(i)(j) = true

		               case (4,26) => answers2(i)(j) = true


		               case (6,36) => answers2(i)(j) = true

		               case (7,38) => answers2(i)(j) = true
		               case (7,21) => answers2(i)(j) = true

		               case (8,37) => answers2(i)(j) = true
		               case (8,22) => answers2(i)(j) = true

		               case (9,17) => answers2(i)(j) = true
		               case (9,34) => answers2(i)(j) = true

		               case (10,33) => answers2(i)(j) = true
		               case (10,18) => answers2(i)(j) = true

		               case (11,23) => answers2(i)(j) = true
		               case (11,32) => answers2(i)(j) = true

		               case (12,31) => answers2(i)(j) = true
		               case (12,24) => answers2(i)(j) = true

		               case (13,25) => answers2(i)(j) = true

		               case (14,27) => answers2(i)(j) = true

		               case (15,30) => answers2(i)(j) = true
		               case (15,19) => answers2(i)(j) = true

		               case (16,20) => answers2(i)(j) = true
		               case (16,29) => answers2(i)(j) = true

		               case (17,9) => answers2(i)(j) = true
		               case (17,34) => answers2(i)(j) = true

		               case (18,10) => answers2(i)(j) = true
		               case (18,33) => answers2(i)(j) = true

		               case (19,15) => answers2(i)(j) = true
		               case (19,30) => answers2(i)(j) = true

		               case (20,16) => answers2(i)(j) = true
		               case (20,29) => answers2(i)(j) = true

		               case (21,7) => answers2(i)(j) = true
		               case (21,38) => answers2(i)(j) = true

		               case (22,8) => answers2(i)(j) = true
		               case (22,37) => answers2(i)(j) = true

		               case (23,11) => answers2(i)(j) = true
		               case (23,32) => answers2(i)(j) = true

		               case (24,12) => answers2(i)(j) = true
		               case (24,31) => answers2(i)(j) = true

		               case (25,13) => answers2(i)(j) = true

		               case (26,4) => answers2(i)(j) = true

		               case (27,14) => answers2(i)(j) = true

		               case (28,3) => answers2(i)(j) = true

		               case (29,16) => answers2(i)(j) = true
		               case (29,20) => answers2(i)(j) = true

 		               case (30,15) => answers2(i)(j) = true
		               case (30,19) => answers2(i)(j) = true

		               case (31,12) => answers2(i)(j) = true
		               case (31,24) => answers2(i)(j) = true

		               case (32,11) => answers2(i)(j) = true
		               case (32,23) => answers2(i)(j) = true

		               case (33,10) => answers2(i)(j) = true
		               case (33,18) => answers2(i)(j) = true

		               case (34,9) => answers2(i)(j) = true
		               case (34,17) => answers2(i)(j) = true

		               case (35,2) => answers2(i)(j) = true

		               case (36,6) => answers2(i)(j) = true

		               case (37,8) => answers2(i)(j) = true

		               case (38,7) => answers2(i)(j) = true
		               case (38,21) => answers2(i)(j) = true

		               case _ => answers2(i)(j) = false
	            } // match
	         } // for j
       } // for i

       for ( i <- 0 until machines.length ) {
       	   val m : DFA = machines(i)
	         val a : Array[Boolean]= answers(i)
       	   testSuiteAcceptance(m,strings,a)
       } // for

       testSuiteEquality(machines,answers2)

       testSuitMinizeSoft(machines,min_machines)
}
