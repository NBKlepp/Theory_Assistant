//::::::::::::::::::::::::::::::::::::::::::::::
/** Author: Nick Klepp
 *  Date: June 6, 2017
 *  The NFA object represents a Non-Deterministic Finite Automaton
 *  @see Introduction to Theory and Computing; Michael Sipser; 3d Ed
 */

package TheoryAssistant

import scala.collection.mutable.Set
import scala.collection.mutable.Map
import TypeDefs._

class NFA() extends FiniteAutomaton
{
  private val DEBUG    = false

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

  private val states   = Set[State]()
  private val alphabet = Set[Symbl]()
  private val delta    = Map[(State,Symbl),Set[State]]()
  private var start    = ""
  private val accept   = Set[State]()
  private var name 	   = "M"
  private var valid    = true
  private var state    = Set[State]()

  def this(states   : Set[State],
           alphabet : Set[Symbl],
           delta    : Map[(State,Symbl),Set[State]],
           start    : State,
           accept   : Set[State],
           name     : String )
  {
 	  this()
	  if (DEBUG) println(s"Making new machine: $name")
   	this.name = name
    this.states   ++= (states union Set(NullState))
  	this.alphabet ++= (alphabet union Set(epsilon))
  	setDelta( delta )
  	setStart( start )
  	setAccept( accept )
  	this.state = findEpsilonStartState()
  	if (DEBUG) println(s"new machine ${toString()}")
  } // this

  def this(states   : Set[State],
           alphabet : Set[Symbl],
           delta    : Set[((State,Symbl),Set[State])],
           start    : State,
           accept   : Set[State],
           name     : String )
  {
   	  this()
	    val newDelta = Map[(State,Symbl),Set[State]]()
	    for ( d <- delta ) newDelta += d._1 -> d._2
	    if (valid) {
        if (DEBUG) println(s"Making new machine: $name")
   	    this.name = name
        this.states   ++= (states union Set(NullState))
  	    this.alphabet ++= (alphabet union Set(epsilon))
  	    setDelta( newDelta )
  	    setStart( start )
  	    setAccept( accept )
  	    this.state = Set(start)
  	    if (DEBUG) println(s"new machine ${toString()}")
	    }
  } // this

  private def setDelta( delta : Map[(State,Symbl),Set[State]])
  {
	   if (DEBUG) println("setting delta.")
	   //Fill in the transitions as specified by delta
     for ( transition <- delta ){
	      if (DEBUG) println(s"Working on $transition")
	      val (input,output) = transition
	      if (validTransition(transition)) this.delta += (input -> output)
	      if (DEBUG) println(s"Map after adding transition: $delta")
	   } // for
	   if (DEBUG) println(s"this.delta: \n ${this.delta}")
	   //Fill in the transitions which aren't specified to the null state.
	   for ( symbl <- alphabet ) {
       for ( state <- states ) {
         val input = (state,symbl)
	    	 if ( !(this.delta contains input) ) this.delta += ((input,Set(NullState)))
	     } // for state
	   } // for symbl
  } // setDelta

  private def setStart( start : State )
  {
    if ( states contains start ) this.start = start
	  else {
	  	 println(s"Invalid start state for $name : $start")
		   println(s"States: $states")
		   valid = false
	  } // else
  } // setStart()

  private def setAccept(accept : Set[State])
  {
  	 if (DEBUG) println(s"Setting accept states with $accept")
  	 if ( (accept -- this.states).size == 0 ) {
	      if (DEBUG) println(s"accept after if: $accept")
	      this.accept ++= accept
	   } // if
	   else {
	   	 for ( state <- accept if ( !(this.states contains state) ) ){
          println(s"Invalid accept state for $name : $state")
       }
		   valid = false
	   } // else
	   if (DEBUG) println(s"this.accept: ${this.accept}")
  } // setAccept


  //:::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
  // The Accessor methods for the private instance variables
  //:::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
  def getStates() = Set[State]() ++ states
  def getAlphabet() = Set[Symbl]() ++ alphabet
  def getDelta() = Map[(State,Symbl),Set[State]]() ++ delta
  def getAcceptStates() = Set[State]() ++ accept
  def getStartState() = start
  def getName() = name
  def isValid() = valid

  //:::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
  /*			The rest of the public API                                   */
  //:::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::

  //:::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
  /* The method to compute a string on a finite automaton.
   * @param string the string to compute
   * @return true if the machine accepts the string, false otherwise
   */
  //:::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
  def compute(string: String) : Boolean =
  {
	   if (DEBUG) println(s"Computing $string on $this")
	   this.state = this.state ++ epsilonHop(this.state)
	   if (DEBUG) println(s"Starting from: ${this.state}")
	   for ( s <- string ) {
       var state = Set[State]()
	     for ( st <- this.state ) {
         val input = (st,s.toString)
	    	 if (DEBUG) println(s"reading input: $input")
	    	 state = state ++ delta(input)
         if (DEBUG) println(s"map says to go to ${delta(input)}")
	     } // for st
	   var epsilonTransitions = epsilonHop(state)
	   this.state = state ++ epsilonTransitions
	   if (DEBUG) println(s"new state: $state")
	   } // for s
	   val finalState = this.state
	   state = Set(start)
	   return (finalState intersect accept ).size != 0
  } // compute

  def equals(m2 : NFA) = DFAify().equals(m2.DFAify())
  def equals(m2 : DFA) = DFAify().equals(m2)

  def kleeneStar() : NFA =
  {
	    if (DEBUG) println(s"starring...")
	    var start = "S"
	    while ( this.states contains start ) start = start + start
	    var states = this.states + start
	    var accept = this.accept + start
	    var delta = Map[(State,Symbl),Set[State]]() // Set[((State,Symbl),Set[State])]()
	    for ( state <- accept if !(state.equals(start)))
	    for ( state <- states ) {
	        for ( a <- alphabet ){
	        	val input = (state,a)
	    	    if ( !(state.equals(start)) ){
	    	        if (  (accept contains state) && a.equals(epsilon) ){
                   delta += input -> ( this.delta(input) ++ Set(this.start) )
                }
	    	        else delta += input -> this.delta(input) // ((input,delta(input)))
	    	    } // if
	    	    else if	  ( a.equals(epsilon) ) {
	    	        delta += input -> Set(this.start) // ((input,Set(this.start)))
	    	    }// else
	        } // for
	    } // for state
	    new NFA(states,this.alphabet,delta,start,accept,s"(${name})*")
  } // KleeneStar

  def union(m2: NFA) : NFA =
  {
    	if (DEBUG) println(s"\n\n\n\tunioning $name with ${m2.getName()}")
    	var start : State = "S"
	    val newM = uniqueify(m2)
	    if (DEBUG) println(s"$newM\n$m2")
	    val states = m2.getStates() ++ newM.getStates() // ++ Set(start)
	    while ( states contains start ) start = start+p
	    states += start
	    val delta = Map[(State,Symbl),Set[State]]()
	    for ( state <- states ){
	        for ( symbol <- alphabet ){
	        	val input = (state,symbol)
	        	if      (newM.getStates() contains state ) delta += input -> newM.delta(input)
	    	    else if (m2.getStates()   contains state ) delta += input -> m2.delta(input)
	    	    else if (symbol.equals(epsilon)          ) delta += input -> Set( newM.getStartState(),m2.getStartState() )
	        } // for symbol
	    } // for state
	    val accept = m2.getAcceptStates() union newM.getAcceptStates()
	    new NFA(states, alphabet,delta,start,accept,name+"_UNION_"+m2.getName())
  } // union

  def complement() : NFA = DFAify().complement().NFAify()

  def concat(m2 : NFA) : NFA =
  {
  	val mm = uniqueify(m2)
	  if (DEBUG) println(s"\n\n\n\tconcating $name and ${m2.getName()}")
	  if (DEBUG) println(s"$this \n $m2 \n $mm")
	  val start = mm.getStartState()
	  val accept = m2.getAcceptStates()
	  val states = (mm.getStates() union m2.getStates()) - NullState
	  val sigma = alphabet - epsilon
	  val delta = Map[(State,Symbl),Set[State]]()

	  for( state <- states ){
	       for ( symbol <- sigma + epsilon ) {
	       	 val input = (state,symbol)
	       	 if ( mm.getAcceptStates contains state ) {
             if ( symbol.equals(epsilon) ) {
               delta += input -> (Set(m2.getStartState()) ++ mm.delta(input))
             } // if
	  	       else delta += input -> mm.delta(input)
	  	     } // if
	  	     else if ( mm.getStates() contains state) {
             delta += input -> mm.delta(input)
	  	     } // else if
	  	     else delta += input -> m2.delta(input)
	       } // for symbol
	  } //for state
	  if (DEBUG) {
	     println(s"concat states: $states")
	     println(s"concat accept: $accept")
	     println(s"concat delta : $delta")
	  }
	  new NFA(states,sigma,delta,start,accept,this.name+"concat"+m2.getName())
  } // concat

  def intersect(m2 : NFA) = DFAify().intersect(m2.DFAify()).NFAify()

  def DFAify() : DFA =
  {
	  if (DEBUG) println(s"DFAifying...")
	  val strt    = epsilonTransitionDFAify(this.start)
	  if (DEBUG) println(s"DFAify start setState: ${strt}")
	  val found : Set[Set[State]]  = Set(strt)
	  val check : Set[Set[State]]  = Set(strt)						// The set of setStates not yet checked
	  val delta1  = Map[(Set[State],Symbl),Set[State]]()
	  val stateNames = Map[Set[State],State]()
	  stateNames += (strt -> setToState(strt))
	  val sigma  = Set[Symbl]()
	  while ( check.size >0 ){					// While there are states we have not yet found the transition for
	        val temp = check.clone								   // The things to check this round
	        if (DEBUG) println(s"checking the following setStates this round: ${temp}")
	        for ( setState <- temp ){								   // For each setState to check this round
	        	  if (DEBUG) println(s"currently checking setState: ${setState}")
	        	  check -= setState									   // Remove this setState from the check list
	  	        for ( a <- alphabet if !(a.equals(epsilon))){							   // For each character in the alphabet
	  	            sigma += a
	  	            val newSetState = setState.flatMap( x => this.delta( x,a ) )
	  	            val epsilonTransitions = newSetState.flatMap(epsilonTransitionDFAify(_))
	  	            newSetState ++= epsilonTransitions
	  	            delta1 += (setState,a) -> newSetState
                  if (DEBUG){
                     println(s"checking transitions from setState: ${setState} on symbol: $a")
                     println(s"Found the following setState without epsilon transitions: ${newSetState}")
                     println(s"Found the follwoing setState using epsilon transitions: ${epsilonTransitions}")
                     println(s"The final setState transition for (${setState},$a): ${newSetState}")
                     println(s"The delta1 now says: ${delta1}")
                  }
	  	            if ( !(found contains newSetState) ){
	  	            	 if (DEBUG) println(s"I found a new state: ${newSetState}")
	  	            	 check += newSetState
	  		             found += newSetState
	  		             stateNames += (newSetState -> setToState(newSetState))
	  	            } // if
	  	        } // for a
	        } // for t
	  } // while
	  if (DEBUG) println(s"Making the DFA")
	  val states = Set[State]()
	  val delta  = Map[(State,Symbl),State]()
	  var start = stateNames(strt)
	  val accept = Set[State]()
	  for ( key <- delta1.keys ) {									// Look at each key in the proto-delta in turn
	      val setState = key._1
	      val fromState = stateNames(setState)  									// The state to add
	      val toState	  = stateNames(delta1(key))
	      val symbl	 = key._2									// The symbl for the transition function
	      states += fromState										// Add the new state to the set created earlier
	      delta += (fromState,symbl) -> toState								// Update the delta function created earlier
	      if (DEBUG){
          println(s"Creating a new transition: ${key}")
          println(s"Working on setState: ${setState}")
          println(s"Transition: ($fromState,$symbl)->$toState")
          println(s"States now: ${states}")
          println(s"Delta now says: ${delta}")
        } // if
	      if ( (setState intersect this.accept).size != 0 ) {				// Update the set of accept states if this setState contained one
	         if (DEBUG) println("Found a new accept state: ${state}")
	         accept += fromState
	      } // if
	  } // for
	  val newM = new DFA(states, sigma/*alphabet*/, delta, start, accept,name+"_DFA")
	  if (DEBUG) println(newM.toString())
	  newM
  } // DFAify

  override def toString() : String =
  {
	  s"$name\n" +
	  s"Start: $start\n" +
	  s"Accept: ${setToString(accept)}\n" +
	  s"Delta: \n$deltaString"
  } // toString

  //:::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
  /*			The private methods.				                                 */
  //:::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
  
  private def epsilonHop(setState : Set[State]) : Set[State] =
  {
    val found   = setState.clone()
    val toCheck = setState.clone()
    for ( state <- setState ) toCheck += state
    if (DEBUG) println(s"Checking for epsilonTransitions from $setState")
    while( toCheck.size != 0 ){
         val checking = toCheck.clone
         for ( state <- checking ){
             if (DEBUG) println(s"hopping from $state")
             val newStates = delta(state,epsilon)
             if (DEBUG) println(s"can hop to $newStates")
             if ( (newStates diff found).size > 0 ){
                 toCheck ++= newStates
                 found   ++= newStates
                 if (DEBUG) println(s"Found some new states to hop from.")
             } // if
         toCheck -= state
         } // for
    } // while
    found
  } // epsilonHop

  private def setToString(set : Set[String]) : String = "{" + set.reduceLeft(_ + ";" +_) + "}"

  private def deltaString : String =
  {
	  var str = ""
	  for ( key <- delta.keys if (!(delta(key).equals(Set(NullState))))) str = str + s"$key => ${setToString(delta(key))}\n"
	  str
  } // deltaString

  private def setToState(set : Set[State]) : State =
  {
	  var newState = ""
	  val newSet = set.toArray
	  for ( state <- newSet ) {
	      newState = if (newSet.indexOf(state)<=newSet.length-2) newState + state + ", " else newState + state
	  }
	  newState
  } // setToState

  def findEpsilonStartState() : Set[State] =
  {
    var state = Set[State](start)
  	 if (DEBUG) println(s"Looking for epsilon transitions from start state.")
  	 if (!(delta(start,epsilon).equals(Set(NullState)))){
	    if (DEBUG) println(s"Found new start using epsilon transitions: ${delta(start,epsilon)}")
	    state = delta(start,epsilon)
	  } // if
	  state
  } // findEpsilonStartState

  def epsilonTransitionDFAify(state : State) : Set[State] =
  {
    if (DEBUG) println(s"epsilon transition from ${state}: ${delta(state,epsilon)}")
    if (!(delta(state,epsilon).equals(Set(NullState)))) {
      if (DEBUG) println(s"Found a good epsilon transition from${state}: ${delta(state,epsilon)}")
      Set(state) ++ delta(state,epsilon)
    } // if
	  else Set(state)
  } // epsilonTransitionDFAify

  def uniqueify(m : NFA) : NFA =
  {
	  val p = "p"
	  if (DEBUG) println(s"uniqueifying $name against ${m.getName()}")
	  val uniq = "-UNIQ-"
	  if ( ((this.states - NullState) intersect (m.states - NullState) ).size != 0 ) {
	     if (DEBUG){
          println(s"${getName()}.states: ${this.getStates()}")
          println(s"${m.getName()}states: ${m.getStates()}")
       }
	     val newStates = Map[State,State]()
	     val states = Set[State]()
	     val delta = Map[(State,Symbl),Set[State]]()
	     for( state <- this.states if !(state.equals(NullState)) ){
	     	var newState = state
	  	    while( m.getStates() contains newState) newState = newState + p
	  	    if ( !(newState.equals(state)) ) {
           while( this.states contains newState ) newState = newState + p
         } // if
	  	    while ( states contains newState) newState = newState + p
	  	    newStates += ( state -> newState)
	  	    states += newState
         if (DEBUG){
           println(s"Uniqueifying state $state.")
           println(s"newState: $newState")
           println(s"newStates: $newStates")
         } // if
	     } // for
	     for( state <- this.states if !(state.equals(NullState)) ){
	  	    for ( symbl <- this.alphabet if !(this.delta(state,symbl).equals(Set(NullState))) ) {
	  	      val newState = newStates(state)
	  	      delta += (newState,symbl) ->
                    this.delta(state,symbl).filterNot( _ == NullState)
                                           .map(x => newStates(x))
	  	    } // for
	     } // for
	     val start = newStates(this.start)
	     val accept = Set[State]()
	     for ( state <- getAcceptStates() ) accept += newStates(state)
	     if (DEBUG) {
         println(s"New machine: \n\tstates: $states \n\tstart: $start \n\taccept: $accept \n\tdelta: $delta")
       }
	     return new NFA(states,alphabet,delta,start,accept, name+"UNIQUED")
	  } // if
	  else return this
  }

  private def validTransition( transition : ((State,Symbl),Set[State]) ) : Boolean =
  {
	  if (DEBUG) println(s"validating transition: $transition")
	  return ( validFromState(transition) && validToStates(transition) && validInputSymbl(transition) && newInput(transition) )
  } // validTransition

  private def validFromState(transition : ((State,Symbl),Set[State]) ) : Boolean =
  {
    if (states contains transition._1._1) return true
    else handleInvalid(1,transition)
  } // validFromState

  private def validToStates(transition : ((State,Symbl),Set[State])) : Boolean =
  {
    if ((transition._2 diff states).size == 0) return true
    else handleInvalid(2,transition)
  } // validToState

  private def validInputSymbl( transition : ((State,Symbl),Set[State]) ) : Boolean =
  {
    if (alphabet contains transition._1._2) return true
    else handleInvalid(3,transition)
  }

  private def newInput( transition : ((State,Symbl),Set[State]))	: Boolean =
  {
    if (delta contains transition._1 ) handleInvalid(4,transition)
    else return true
  }

  private def handleInvalid(i : Int, transition : ((State,Symbl),Set[State])) : Boolean =
  {
    val fromState  = transition._1._1
  	val inputSymbl = transition._1._2
  	val toStates    = transition._2
    i match{
  	   case 1 => {
  	   	 println(s"Invalid transition: delta($fromState,$inputSymbl)->$toStates)"+
                s" :: $fromState not in the set of states for ${name}.")
  		   valid = false
  	   } // case 1
  	   case 2 => {
  	   	 for ( state <- toStates if !(states contains state ) ) {
          println(s"Invalid transition: delta($fromState,$inputSymbl)->$toStates)"+
                  s" :: $state not in the set of states for ${name}.")
        } // for
  		   valid = false
  	   } // case 2
  	   case 3 => {
  	     println(s"Invalid transition: delta($fromState,$inputSymbl)->$toStates)"+
                s" :: $inputSymbl not in the alphabet for ${name}.")
  		   valid = false
  	   } // case 3
  	   case 4 => {
  	     println(s"Invalid transition: delta($fromState,$inputSymbl)->$toStates)"+
  	        	   s" :: transition already specified for input ${transition._1} for ${name}.")
  	     valid = false
  	   } // case 4
  	 }
  false
  } // handleInvalid

}// NFA

object NFATestMethods{

  val DEBUG = false

  def testAcceptance(m1 : NFA , s : String , expRes : Boolean){
  	   m1.compute(s) == expRes
  } // testAcceptance

  def testEquality(m1 : NFA , m2 : NFA , expRes : Boolean){
  	   m1.equals(m2) == expRes
  } // testEquality

  def testSuiteEquality(machines : Array[NFA], answers : Array[Array[Boolean]]){
    var res = true
  	for ( i <- 0 until answers.length ) {
      for ( j <- i until answers.length ) {
        val testRes = machines(i).equals(machines(j))
        val expRes  = answers(i)(j)
        val m1s     = machines(i).toString()
        val m2s     = machines(j).toString()
        if ( !(testRes == expRes) ){
          println(s"Test failed for equality. M1: ${m1s}\nM2: ${m2s}\nExpected: ${expRes}\nObserved: ${testRes}")
        } // if
	    } // for j
	  } // for i
  } // testSuiteEqualitydef

  def testSuiteEquality2(machines : Array[DFA], machines2 : Array[DFA] ) =
  {
    var res = true
  	 for ( i <- 0 until machines.length ) {
	    val m1 = machines(i).getName()
	    val m2 = machines2(i).getName()
	    println(s"Testing equality for $m1 and $m2")
	    if ( !(machines(i).equals(machines2(i))) ) {
	    	 println(s"\tBad DFAify equality: $m1 != $m2" )
	      println(machines(i))
	      println(machines2(i))
	      res = false
	    } // if
	    else println(s"\ttestSuiteEquality2 passed for ${machines(i).getName()}"+
                   s" and ${machines2(i).getName()}")
	  }
	  if (res) println("test suite equality 2 passed.")
  } // testSuiteEqualitydef

  def testSuiteEquality3(machines : Array[NFA], machines2 : Array[DFA] ) =
  {
    var res = true
  	for ( i <- 0 until machines.length ) {
      val m1 = machines(i).getName()
      val m2 = machines2(i).getName()
      println(s"Testing equality for $m1 and $m2")
      if ( !(machines(i).equals(machines2(i))) ) {
     	  println(s"\tBad DFAify equality: $m1 != $m2" )
  	    println(machines(i))
  	    println(machines2(i))
  	    res = false
  	  } // if
  	  else println(s"\ttestSuiteEquality2 passed for ${machines(i).getName()} and ${machines2(i).getName()}")
    }
  	if (res) println("test suite equality 2 passed.")
  } // testSuiteEqualitydef

  def testSuiteAcceptance(machine : NFA, strings : Array[String], answers : Array[Boolean])
  {
    if (DEBUG) println(s"\n\n\n\n\\n**************Test Suite Acceptance***************\n$machine")
   	var pass = true
   	for ( i <- 0 until answers.length ) {
      val string = strings(i)
     	val testRes = machine.compute(string)
      val expRes  = answers(i)
      val m1s     = machine.toString()
     	if ( !(testRes == expRes) ){
        println(s"Test failed for acceptance."+
                s" \nString: ${string}\nMachine: \n${m1s}Expected: ${expRes}\nObserved: ${testRes}\n\n")
        pass = false
      } // if
  	} // for
  	if (pass) println(s"Acceptance suite passed for ${machine.getName()}")
  } // testSuiteEquality

  def testSuiteAcceptance2(machine : DFA, strings : Array[String], answers : Array[Boolean])
  {
    var pass = true
   	for ( i <- 0 until answers.length ) {
      val string = strings(i)
      val testRes = machine.compute(string)
      val expRes  = answers(i)
      val m1s     = machine.toString()
     	if ( !(testRes == expRes) ){
        println(s"Test failed for acceptance."+
                s" \nString: ${string}\nMachine: \n${m1s}Expected: ${expRes}\nObserved: ${testRes}\n\n")
        pass = false
      } // if
  	} // for
  	if (pass) println(s"Acceptance suite passed for ${machine.getName()}")
  } // testSuiteEquality

} // NFATestMethods

object NFATester extends App{

  import NFATestMethods._

  def mapFromSet( set : Set[((State,Symbl),Set[State])] ) : Map[(State,Symbl),Set[State]] =
  {
    val map = Map[(State,Symbl),Set[State]]()
    for ( input <- set ) map += (input._1 -> input._2)
	  map
  } // mapFromSet

  def mapFromSet2( set : Set[((State,Symbl),State)] ) : Map[(State,Symbl),State] =
  {
    val map = Map[(State,Symbl),State]()
  	for ( input <- set ) map += (input._1 -> input._2)
	  map
  } // mapFromSeT2

  val DEBUG = false

  val sigma   = Set("0","1")

  val states1 = Set("0","1")											//even length
  val delta1  = mapFromSet(
    Set(
      (("0","0"),Set("1")),
      (("0","1"),Set("1")),
      (("1","0"),Set("0")),
      (("1","1"),Set("0"))))
  val start1  = "0"
  val accept1 = Set("0")

  val states1DFA = Set("0","1")										//All even length strings
  val sigma1DFA  = Set("0","1")
  val delta1DFA  = mapFromSet2(
    Set(
      (("0","0"),"1"),
      (("0","1"),"1"),
      (("1","0"),"0"),
      (("1","1"),"0")))
  val start1DFA  = "0"
  val accept1DFA = Set("0")
  val states2 = Set("0","00","10","01","11")									//even 0s OR odd 1s
  val delta2  = mapFromSet(
    Set(
      (("0",epsilon),Set("00","10")),
      (("00","0"   ),Set("01"     )),
      (("00","1"   ),Set("00"     )),
      (("01","0"   ),Set("00"     )),
      (("01","1"   ),Set("01"     )),
      (("10","0"   ),Set("10"     )),
      (("10","1"   ),Set("11"     )),
      (("11","0"   ),Set("11"     )),
      (("11","1"   ),Set("10"     ))))
  val start2  = "0"
  val accept2 = Set("00","11")
  val states2DFA = Set("00","01","10","11")										//Even 0's OR odd 1's
  val delta2DFA  = mapFromSet2(
    Set(
      (("00","0"),"10"),
      (("00","1"),"01"),
      (("10","0"),"00"),
      (("10","1"),"11"),
  	  (("11","1"),"10"),
      (("11","0"),"01"),
      (("01","1"),"00"),
      (("01","0"),"11")))
  val start2DFA  = "00"
  val accept2DFA = Set("00","01","11")
  val states2_1 = Set("00","01")											//even 0s
  val delta2_1  = mapFromSet(
    Set(
      (("00","0"),Set("01")),
      (("00","1"),Set("00")),
      (("01","0"),Set("00")),
      (("01","1"),Set("01"))))
  val start2_1  = "00"
  val accept2_1 = Set("00")
  val states2_2 = Set("10","11")											//odd 1s
  val delta2_2  = mapFromSet(
    Set(
      (("10","1"),Set("11")),
      (("10","0"),Set("10")),
      (("11","1"),Set("10")),
      (("11","0"),Set("11"))))
  val start2_2  = "10"
  val accept2_2 = Set("11")
  val states3 = Set("0","00","10","01","11")									//even 0s OR even 1s
  val delta3  = mapFromSet(
    Set(
      (("0",epsilon),Set("00","10")),
		  (("00","0"   ),Set("01"     )),
      (("00","1"   ),Set("00"     )),
      (("01","0"   ),Set("00"     )),
      (("01","1"   ),Set("01"     )),
		  (("10","0"   ),Set("10"     )),
      (("10","1"   ),Set("11"     )),
      (("11","0"   ),Set("11"     )),
      (("11","1"   ),Set("10"     ))))
  val start3  = "0"
  val accept3 = Set("00","10")
  val states3DFA = Set("00","01","10","11")										//Even 0's OR even 1's
  val delta3DFA  = mapFromSet2(
    Set(
      (("00","0"),"10"),
      (("00","1"),"01"),
      (("10","0"),"00"),
      (("10","1"),"11"),
  	  (("11","1"),"10"),
      (("11","0"),"01"),
      (("01","1"),"00"),
      (("01","0"),"11")))
  val start3DFA  = "00"
  val accept3DFA = Set("00","01","10")
  val states4 = Set("0","00","10","01","11")									//odd 0s OR odd 1s
  val delta4  = mapFromSet(
    Set(
      (("0",epsilon),Set("00","10")),
			(("00","0"   ),Set("01"     )),
      (("00","1"   ),Set("00"     )),
      (("01","0"   ),Set("00"     )),
      (("01","1"   ),Set("01"     )),
			(("10","0"   ),Set("10"     )),
      (("10","1"   ),Set("11"     )),
      (("11","0"   ),Set("11"     )),
      (("11","1"   ),Set("10"     ))))
  val start4  = "0"
  val accept4 = Set("01","11")
  val states4DFA = Set("00","01","10","11")										//odd 0's OR odd 1's
  val delta4DFA  = mapFromSet2(
    Set(
      (("00","0"),"10"),
      (("00","1"),"01"),
      (("10","0"),"00"),
      (("10","1"),"11"),
    	(("11","1"),"10"),
      (("11","0"),"01"),
      (("01","1"),"00"),
      (("01","0"),"11")))
  val start4DFA  = "00"
  val accept4DFA = Set("10","01","11")
  val states5 = Set("0","00","10","01","11")									//odd 0s OR even 1s
  val delta5  = mapFromSet(
    Set(
      (("0",epsilon),Set("00","10")),
		  (("00","0"   ),Set("01"     )),
      (("00","1"   ),Set("00"     )),
      (("01","0"   ),Set("00"     )),
      (("01","1"   ),Set("01"     )),
		  (("10","0"   ),Set("10"     )),
      (("10","1"   ),Set("11"     )),
      (("11","0"   ),Set("11"     )),
      (("11","1"   ),Set("10"     ))))
  val start5  = "0"
  val accept5 = Set("01","10")
  val states5DFA = Set("00","01","10","11")										//odd 0's OR even 1's
  val delta5DFA  = mapFromSet2(
    Set(
      (("00","0"),"10"),
      (("00","1"),"01"),
      (("10","0"),"00"),
      (("10","1"),"11"),
  	  (("11","1"),"10"),
      (("11","0"),"01"),
      (("01","1"),"00"),
      (("01","0"),"11")))
  val start5DFA  = "00"
  val accept5DFA = Set("10","00","11")
  val states6 = Set("0","1","2","3","4")
  val delta6  = mapFromSet(
    Set(
      (("0","0"),Set("0","1")),
      (("0","1"),Set("0"    )),
      (("1","1"),Set("2"    )),
			(("2","1"),Set("3"    )),
			(("3","0"),Set("4"    )),
			(("4","0"),Set("4"    )),
      (("4","1"),Set("4"    ))))
  val start6  = "0"
  val accept6 = Set("4")
  val states6DFA = Set("0","1","2","3","4","5","6","7")
  val delta6DFA  = mapFromSet2(
    Set(
      (("0","1"),"0"),
      (("0","0"),"1"),
			(("1","1"),"2"),
      (("1","0"),"1"),
			(("2","1"),"3"),
      (("2","0"),"1"),
			(("3","1"),"0"),
      (("3","0"),"4"),
			(("4","1"),"5"),
      (("4","0"),"4"),
			(("5","1"),"6"),
      (("5","0"),"4"),
			(("6","1"),"7"),
      (("6","0"),"4"),
			(("7","1"),"7"),
      (("7","0"),"4")))
  val start6DFA  = "0"
  val accept6DFA = Set("4","5","6","7")
  val states7 = Set("0","1","2")
  val delta7  = mapFromSet(
    Set(
      (("0","1"),Set("0","1")),
      (("0","0"),Set("0"    )),
    	(("1","1"),Set("2"    ))))
  val start7  = "0"
  val accept7 = Set("2")
  val states7DFA = Set("0","1","2")
  val delta7DFA  = mapFromSet2(
    Set(
      (("0","1"),"1"),
      (("0","0"),"0"),
			(("1","1"),"2"),
      (("1","0"),"0"),
			(("2","1"),"2"),
      (("2","0"),"0")))
  val start7DFA  = "0"
  val accept7DFA = Set("2")
  val states8 = Set("1","2","3","4","5")
  val delta8  = mapFromSet(
    Set(
      (("1","0"),Set("1","2")),
      (("1","1"),Set("1","4")),
			(("2","0"),Set("3"    )),
			(("3","0"),Set("3"    )),
      (("3","1"),Set("3"    )),
      (("4","1"),Set("5"    )),
			(("5","0"),Set("5"    )),
      (("5","1"),Set("5"    ))))
  val start8  = "1"
  val accept8 = Set("3","5")
  val states8DFA = Set("1","12","14","123","145","143","125","1253","1453")
  val delta8DFA  = mapFromSet2(
    Set(
      (("1","1"),"14"     ),(("1","0")   ,"12"  ),
			(("12","1"),"14"    ),(("12","0")  ,"123" ),
			(("14","1"),"145"   ),(("14","0")  ,"12"  ),
			(("123","1"),"143"  ),(("123","0") ,"123" ),
			(("145","1"),"145"  ),(("145","0") ,"125" ),
			(("143","1"),"1453" ),(("143","0") ,"123" ),
			(("125","1"),"145"  ),(("125","0") ,"1253"),
			(("1253","1"),"1453"),(("1253","0"),"1253"),
			(("1453","1"),"1453"),(("1453","0"),"1253")))
  val start8DFA  = "1"
  val accept8DFA = Set("123","145","143","125","1253","1453")
  val statesS = Set("0","1")
  val deltaS  = mapFromSet(
    Set(
      (("0","0"),Set("1")),
      (("0","1"),Set("1"))))
  val startS  = "0"
  val acceptS = Set("1")
  val statesEO = Set("0","1")
  val startEO  = "0"
  val deltaE0  = mapFromSet(
    Set(
      (("0","0"),Set("1")),
      (("0","1"),Set("0")),
			(("1","0"),Set("0")),
      (("1","1"),Set("1"))))
  val acceptE0 = Set("0")
  val deltaO0  = mapFromSet(
    Set(
      (("0","0"),Set("1")),
      (("0","1"),Set("0")),
			(("1","0"),Set("0")),
      (("1","1"),Set("1"))))
  val acceptO0 = Set("1")
  val deltaE1  = mapFromSet(
    Set(
      (("0","0"),Set("0")),
      (("0","1"),Set("1")),
			(("1","0"),Set("1")),
      (("1","1"),Set("0"))))
  val acceptE1 = Set("0")
  val deltaO1  = mapFromSet(
    Set(
      (("0","0"),Set("0")),
      (("0","1"),Set("1")),
			(("1","0"),Set("1")),
      (("1","1"),Set("0"))))
  val acceptO1 = Set("1")
  val states11 = Set("0","1","2")
  val start11  = "0"
  val delta11  = mapFromSet(
    Set(
      (("0","1"),Set("1")),
      (("1","1"),Set("2"))))
  val accept11 = Set("2")
  val states00 = Set("0","1","2")
  val start00  = "0"
  val delta00  = mapFromSet(
    Set(
      (("0","0"),Set("1")),
      (("1","0"),Set("2"))))
  val accept00 = Set("2")
  if (DEBUG) println("making m1")
  val m1   = new NFA(states1,sigma,delta1,start1,accept1,"m1")
  if (DEBUG) println("m1 done.")
  val m1d  = new DFA(states1DFA,sigma,delta1DFA,start1DFA,accept1DFA,"m1d")
  if (DEBUG) println("m1d done.")
  val m1dd = m1.DFAify()
  if (DEBUG) println("m1 done.")
  val m2   = new NFA(states2,sigma,delta2,start2,accept2,"m2")
  val m2d  = new DFA(states2DFA,sigma,delta2DFA,start2DFA,accept2DFA,"m2d")
  val m2dd = m2.DFAify()
  val m2_1 = new NFA(states2_1,sigma,delta2_1,start2_1,accept2_1,"m2_1")
  val m2_2 = new NFA(states2_2,sigma,delta2_2,start2_2,accept2_2,"m2_2")
  val m2U	= m2_1.union(m2_2)
  if (DEBUG) println("m2 done.")
  val m3   = new NFA(states3,sigma,delta3,start3,accept3,"m3")
  if (DEBUG) println("m3 done.")
  val m3d  = new DFA(states3DFA,sigma,delta3DFA,start3DFA,accept3DFA,"m3d")
  if (DEBUG) println("m3d done.")
  val m3dd = m3.DFAify()
  if (DEBUG) println("m3 done.")
  val m4   = new NFA(states4,sigma,delta4,start4,accept4,"m4")
  val m4d  = new DFA(states4DFA,sigma,delta4DFA,start4DFA,accept4DFA,"m4d")
  val m4dd = m4.DFAify()
  if (DEBUG) println("m4 done.")
  val m5   = new NFA(states5,sigma,delta5,start5,accept5,"m5")
  val m5d  = new DFA(states5DFA,sigma,delta5DFA,start5DFA,accept5DFA,"m5d")
  val m5dd = m5.DFAify()
  if (DEBUG) println("m5 done.")
  val m6   = new NFA(states6,sigma,delta6,start6,accept6,"m6")
  if (DEBUG) println("m6 done.")
  val m6d  = new DFA(states6DFA,sigma,delta6DFA,start6DFA,accept6DFA,"m6d")
  if (DEBUG) println("m6d done.")
  val m6dd = m6.DFAify()
  if (DEBUG) println("m6 done.")
  val m7   = new NFA(states7,sigma,delta7,start7,accept7,"m7")
  val m7d  = new DFA(states7DFA,sigma,delta7DFA,start7DFA,accept7DFA,"m7d")
  val m7dd = m7.DFAify()
  if (DEBUG) println("m7 done.")
  val m8   = new NFA(states8,sigma,delta8,start8,accept8,"m8")
  val m8d  = new DFA(states8DFA,sigma,delta8DFA,start8DFA,accept8DFA,"m8d")
  val m8dd = m8.DFAify()
  if (DEBUG) println("m8 done.")
  val mS   = new NFA(statesS,sigma,deltaS,startS,acceptS,"S")
  if (DEBUG) println("mS done.")
  val mE0	= new NFA(statesEO,sigma,deltaE0,startEO,acceptE0,"E0")
  if (DEBUG) println("mE0 done.")
  val mO0	= new NFA(statesEO,sigma,deltaO0,startEO,acceptO0,"O0")
  if (DEBUG) println("mO0 done.")
  val mE1  = new NFA(statesEO,sigma,deltaE1,startEO,acceptE1,"E1")
  if (DEBUG) println("mE1 done.")
  val mO1  = new NFA(statesEO,sigma,deltaO1,startEO,acceptO1,"O1")
  if (DEBUG) println("mO1 done.")
  val m_11  = new NFA(states11,sigma,delta11,start11,accept11,"11")
  if (DEBUG) println("m_11 done.")
  val m_00  = new NFA(states00,sigma,delta00,start00,accept00,"00")
  if (DEBUG) println("m_00 done.")
  val m9   = mS.concat(mS).kleeneStar()	// (SS)*
  if (DEBUG) println("m9 done.")
  val m10  = mE0.union(mO1)		// equal to m2
  if (DEBUG) println("m10 done.")
  val m11  = mE0.union(mE1)		// equal to m3
  if (DEBUG) println("m11 done.")
  val m12  = mO0.union(mO1)		// equal to m4
  if (DEBUG) println("m12 done.")
  val m13	= mO0.union(mE1)		// equal to m5
  if (DEBUG) println("m13 done.")
  println(mS.kleeneStar())
  println(mS.kleeneStar().concat(m_11))
  println(mS.kleeneStar().concat(m_11).concat(mS.kleeneStar()))
  println(mS.kleeneStar().concat(m_00).concat(mS.kleeneStar()))
  val m14	= mS.kleeneStar().concat(m6).concat(mS.kleeneStar()) // equal to m6
  if (DEBUG) println("m14 done.")
  val m15  = mS.kleeneStar().concat(m_11)			      // equal to m
  if (DEBUG) println("m15 done.")
  val m16 = mS.kleeneStar()
              .concat(m_11)
              .concat(mS.kleeneStar())
              .union(mS.kleeneStar()
              .concat(m_00)
              .concat(mS.kleeneStar())) // equal to m8
  if (DEBUG) println("m16													   done.")
  val strings = Array("0101","01010","01011101","","111111","1111111","0101101","00110","000110")
  println(s"//::::::::::::::\n**Testing String Acceptance**\n//::::::::::::::")
  val answers = Array.ofDim[Array[Boolean]](16)
    for ( i <- 0 until 16 ){
	    i+1 match {
	  	 case 1 => answers(i) = Array(true,false,true,true,true,false,false,false,true)
		   case 2 => answers(i) = Array(true,false,true,true,true,true,false,false,true)
		   case 3 => answers(i) = Array(true,true,false,true,true,true,true,true,true)
		   case 4 => answers(i) = Array(false,true,true,false,false,true,true,true,false)
		   case 5 => answers(i) = Array(true,true,true,true,true,false,true,true,true)
		   case 6 => answers(i) = Array(false,false,false,false,false,false,true,true,true)
		   case 7 => answers(i) = Array(false,false,false,false,true,true,false,false,false)
		   case 8 => answers(i) = Array(false,false,true,false,true,true,true,true,true)
		   case _ => answers(i) = answers(i-8)
      }// match
    } // for
    val machines = Array(m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16)
    val machines2 = Array(m1d,m2d,m3d,m4d,m5d,m6d,m7d,m8d)
    val machines3 = Array(m1dd,m2dd,m3dd,m4dd,m5dd,m6dd,m7dd,m8dd)
    val machines4 = machines.slice(0,7)
    for ( i <- 0 until machines2.length ) {
    	   //val m = machines(i)
	    val mm = machines2(i)
	    val mmm = machines3(i)
	    val a = answers(i)
       	   //testSuiteAcceptance(m,strings,a)
	    testSuiteAcceptance2(mm,strings,a)
	    testSuiteAcceptance2(mmm,strings,a)
    } // for
    for ( i <- 0 until machines.length ) {
    	   testSuiteAcceptance(machines(i),strings,answers(i))
    } // for
    testSuiteEquality3(machines4,machines2)
    testSuiteEquality2(machines2,machines3)
    testSuiteEquality3(machines4,machines3)
}
