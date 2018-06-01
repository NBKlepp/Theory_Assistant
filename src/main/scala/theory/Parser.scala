//TODO : parsePDA and parseTM

package theory

import scala.collection.mutable.{Set,Map}
import TypeDefs._
import scala.io.Source
import java.io.{PrintWriter,FileWriter}
import java.io.FileNotFoundException
import java.nio.file.{Paths,Files}

final case class NoSubmissionException(private val fil : String = "",
                                       private val c : Throwable = None.orNull)
                                       extends Exception(fil,c)

final case class ParserException(private val line: String = "",
                                 private val c : Throwable = None.orNull)
                                 extends Exception(line,c)

class Parser(){

  /************************************************************************
   *                 The Private Instance Variables                       *
   ************************************************************************/

  val _DFA = 0
  val _NFA = 1
  val _PDA = 2
  val _TM  = 3
  val DEBUG = true

  /************************************************************************
   *                      The Public Methods                              *
   ************************************************************************/

  @throws(classOf[NoSubmissionException])
  @throws(classOf[ParserException])
  def parseFile(fil : String, typ : Int) : FiniteAutomaton =
  {
      //Make sure there is a submission file
      if(! Files.exists(Paths.get(fil))) throw new NoSubmissionException(fil)

      val lines = Source.fromFile(fil).
                         mkString.
                         filterNot((x: Char) => x.isWhitespace).
                         split(";")

      try{
        typ match{
          case _DFA => return parseDFA(lines)
          case _NFA => return parseNFA(lines)
        }
      }catch{
        case pe  : ParserException => throw pe
      } // catch
  } // parseFile

  @throws(classOf[ParserException])
  def parseDFA(lines : Array[String]) : DFA =
  {
      var states   = Set[State]()
      var alphabet = Set[Symbl]()
      var delta    = Map[(State,Symbl),State]()
      var start    = ""
      var accept   = Set[State]()
      var name 	   = ""

      val deltaLines = Set[String]()

      for (lline <- lines){
        val line = lline.replace("\\e",epsilon)
        if (line.length > 0 ){
          line.charAt(0) match{
            case 'T' => name = line
            case 'Q' => states = makeStates(line)
            case 'S' => alphabet = makeSigma(line)
            case 'd' => deltaLines += line
            case 'q' => start = makeStart(line)
            case 'F' => accept = makeAccept(line)
            case _   => throw new ParserException(line)
          }
        }
      } // for line

      try{
        delta = makeDFA_Delta(deltaLines.toArray)
      }catch{
        case pe : ParserException => throw pe
      } // catch

      try{
        validateDeltaDFA(states,alphabet,delta)
        validateStart(states,start)
        validateAccept(states,accept)
      }catch{
        case pe : ParserException => throw pe
      }//catch
      return new DFA(states,alphabet,delta,start,accept)
  } // parseDFA

  @throws(classOf[ParserException])
  def parseNFA(lines : Array[String]) : NFA =
  {
    var states   = Set[State]()
    var alphabet = Set[Symbl]()
    var delta    = Map[(State,Symbl),Set[State]]()
    var start    = ""
    var accept   = Set[State]()
    var name 	   = ""

    val deltaLines = Set[String]()

    for (lline <- lines){
      val line = lline.replace("\\e",epsilon)
      if (line.length > 0 ){
        line.charAt(0) match{
          case 'T' => name = line
          case 'Q' => states = makeStates(line)
          case 'S' => alphabet = makeSigma(line)
          case 'd' => deltaLines += line
          case 'q' => start = makeStart(line)
          case 'F' => accept = makeAccept(line)
          case _   => throw new ParserException(line)
        }
      }
    } // for line

    try{
      delta = makeNFA_Delta(deltaLines.toArray)
    }catch{
      case pe : ParserException => throw pe
    } // catch

    try{
      validateDeltaNFA(states,alphabet,delta)
      validateStart(states,start)
      validateAccept(states,accept)
    }catch{
      case pe : ParserException => throw pe
    } // catch
    return new NFA(states,alphabet,delta,start,accept,name)
  } // parseNFA

  /***********************************************************************
   *                The private instance methods                         *
   ***********************************************************************/

  private def makeStates(line : String) : Set[State] = {
    if (DEBUG) println(s"Making states.")
    val states = Set[State]()
    val lline = line.filterNot((x : Char) => x.isWhitespace)
    var tokens = lline.replace("Q={","").
                      replace("}","" ).
                      split(",")
    for (t <- tokens){
      states += t
    } // for
    return states
  } // makeStates

  private def makeSigma(line : String) : Set[Symbl] = {
    if (DEBUG) println(s"Making sigma.")
    val sigma = Set[Symbl]()
    val lline = line.filterNot((x : Char) => x.isWhitespace)
    var tokens = lline.replace("S={","").
                      replace("}","" ).
                      split(",")
    for (t <- tokens){
      sigma += t
    } // for
    return sigma
  } // makeSigma

  private def makeStart(line : String) : String = {
    if (DEBUG) println(s"Making sigma.")
    val lline = line.filterNot((x : Char) => x.isWhitespace)
    var start = lline.replace("q0=","")
    return start
  } // makeStart

  private def makeAccept(line : String) : Set[State] = {
    if (DEBUG) println(s"Making states.")
    val accept = Set[State]()
    val lline = line.filterNot((x : Char) => x.isWhitespace)
    var tokens = lline.replace("F={","").
                      replace("}","" ).
                      split(",")
    for (t <- tokens){
      accept += t
    } // for
    return accept
  } // makeAccept

  @throws(classOf[ParserException])
  private def makeDFA_Delta(deltaLines : Array[String]) : Map[(State,Symbl),State] =
  {
    val delta = Map[(State,Symbl),State]()
    val ddeltaLines = deltaLines.map(x => x.filterNot((y : Char) => y.isWhitespace)).
                                 map(x=>x.replace("d(","")).
                                 map(x=>x.replace(")=",",")).
                                 map(x=>x.split(","))
    for(t <- 0 until ddeltaLines.size){
      if ( ddeltaLines(t).length < 3 ) {
        throw new ParserException(s"Bad transition spec: ${deltaLines(t)}")
      }
      val (q,a,r) = (ddeltaLines(t)(0),ddeltaLines(t)(1),ddeltaLines(t)(2))
      delta += (q,a) -> r
    }
    return delta
  } // makeDFA_Delta

  @throws(classOf[ParserException])
  private def makeNFA_Delta(deltaLines : Array[String]) : Map[(State,Symbl),Set[State]] =
  {
    val delta = Map[(State,Symbl),Set[State]]()
    val ddeltaLines = deltaLines.map(x => x.filterNot((y : Char) => y.isWhitespace)).
                                 map(x=>x.replace("d(","")).
                                 map(x=>x.replace(")={","#")).
                                 map(x=>x.replace("})","")).
                                 map(x=>x.split("#"))
    for(t <- 0 until ddeltaLines.size){
      if ( ddeltaLines(t).length < 2 ) {
        throw new ParserException(s"Bad transition spec: ${deltaLines(t)}")
      }
      val (input,output) = (ddeltaLines(t)(0),ddeltaLines(t)(1))
      val iinput = input.split(",")
      var ooutput = output.split(",").toSet
      var oooutput = collection.mutable.Set(ooutput.toArray:_*)
      if (iinput.length < 2 ) {
        throw new ParserException(s"Bad transition spec: ${deltaLines(t)}")
      }
      val q = iinput(0)
      val a = iinput(1)

      delta += (q,a) -> oooutput
    }
    return delta
  } // makeDFA_Delta

  @throws(classOf[ParserException])
  def validateDeltaDFA(states   : Set[State],
                       alphabet : Set[Symbl],
                       delta    : Map[(State,Symbl),State]){
    for((k,r) <- delta){
      val q = k._1
      val a = k._2
      if ( !(states   contains q) ||
           !(states   contains r) ||
           !(alphabet contains a)    ){
             throw new ParserException(s"Bad Transition spec: d($q,$a)=$r")
           } // if
    } // for
  } // validateDeltaDFA

  @throws(classOf[ParserException])
  def validateDeltaNFA(states   : Set[State],
                       alphabet : Set[Symbl],
                       delta    : Map[(State,Symbl),Set[State]]){
    for((k,s) <- delta){
      val q = k._1
      val a = k._2
      if ( !(states   contains q     ) ||
           !(s        subsetOf states) ||
           !(alphabet contains a     )    ){
             throw new ParserException(s"Bad Transition spec: d($q,$a)=$s")
           } // if
    } // for
  } // validateDeltaDFA

  @throws(classOf[ParserException])
  def validateStart(states : Set[State],start : State){
    if(!(states contains start)) {
      throw new ParserException(s"Bad Start state : ${start}")
    } // if
  } // validateStart

  @throws(classOf[ParserException])
  def validateAccept(states : Set[State], accept : Set[State]){
    if (!(accept subsetOf states)){
      throw new ParserException(s"Bad accept state set : ${accept}")
    } // if
  } // validateAccept

} // Parser
