/*
  It would probably be best to write a suite of tests that you import
  into the grader so that you don't have to do the same thing over
  and over again. Just an idea.

  Note that we also need to provide the file to find the assignments we want
  to grade with this autograder. That's not the case with the other autograder.

  We coul have hard coded the above information if we wanted to. I didn't.
*/
import TheoryAssistant._
import net.liftweb.json.JsonAST._
import net.liftweb.json.Extraction._
import net.liftweb.json.Printer._
import scala.io.Source
import scala.collection.mutable.Map

object SampleGrader extends App{

  //sscores is really just for the autolab convention, where the format
  //has to be a dictionary {"scores" : {"1a":10,"1b":10,...}}
  val sscores = Map[String,scala.collection.immutable.Map[String,Int]]()

  //we could just use scores if we didn't want to use the autolab convention
  val scores = Map[String,Int]()

  //the parser we'll use to parse our machines with
  val p = new Parser()
  val exercises = args(0)

  /*
    Just loop through the assignment file parsing each submission machine
    and solution machine in turn and comparing them. If they're the same,
    good. If not, tell the student why not. 
  */
  for (line <- Source.fromFile(exercises).getLines){
    print(s"\n\nGrading exercise ${line}...\n")
    var points = 10
    try{
      val sub = p.parseDFA(s"data/submission/${line}")
      val sol = p.parseDFA(s"data/solutions/${line}")

      if ( sub.equals(sol) ) {
         println( s"${line} passed evaluation" )
         scores += line -> points
      } // if

      else {

        println(s"Your submission: \n${sub}")
        val excess_machine = sub.intersect(sol.complement()).minimize()
        val missed_machine = sol.intersect(sub.complement()).minimize()
        if ( !( excess_machine.recognizesEmptyLanguage() )) {
          println(s"-5 points.\n"                                    +
                  s"Your submission accepted some strings that it "  +
                  s"shouldn't have accepted.\n"                      +
                  s"This machine accepts those excessive strings.\n" +
                  s"${excess_machine}")
          points -= 5
        } // if
        if ( !( missed_machine.recognizesEmptyLanguage() )) {
          println(s"-5 points\n"                                           +
                  s"Your submission did not accept all the strings that" +
                  s"it should have.\n "                                  +
                  s"The following machine recognizes those strings: \n"  +
                  s"${missed_machine}")
          points -= 5
        } // if
        scores += line -> points
      } // else
    }catch{
      case pe : ParserException => {println(s"\n${pe}\n");
                                    scores += line -> 0;}
      case nse : NoSubmissionException => {println(s"\n${nse}\n");
                                           scores += line -> 0;}
      case me : MachineException => {println(s"\n${me}\n"); scores += line -> 0}
    } // catch
  } // for
  implicit val formats = net.liftweb.json.DefaultFormats
  sscores += "scores" -> scores.toMap
  println(compact(render(decompose(sscores.toMap))))
} // SampleGrader
