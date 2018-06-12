/*
  It would probably be best to write a suite of tests that you import
  into the grader so that you don't have to do the same thing over
  and over again. Just an idea.
*/
import TheoryAssistant._
import net.liftweb.json.JsonAST._
import net.liftweb.json.Extraction._
import net.liftweb.json.Printer._
import scala.io.Source
import scala.collection.mutable.Map

object SampleGrader2 extends App{

  /******************************************************************
  * The method to compare a solution to a submission DFA             *
  * It prints out some important information, and returns the points *
  * awarded for the submission for this exercise.                    *
  * Writing the feedback to a file is usually more helpful than just *
  * printing the feedback to the standard out, as you can give the   *
  * feedback back to the student if you write it to a file.          *
  *                                                                  *
  * TBH the only reason I wrote this method was so that I didn't     *
  * have to write multiple try/catch blocks in the code...           *
  *                                                                  *                                                                     *
  * @param sol : The solution machine, a DFA objet                   *
  * @param exercse : The exercise you're evaluating                  *
  * @return points : The number of points awarded for the submission *
  * @throws ParserException : If the machine syntax is invalid       *
  * @throws NoSubmissionException : If no submission is found.       *
  * @throws MachineException : If the alphabets don't match          *
  *******************************************************************/
  def compareDFAs(sol : DFA , exercise : String) : Int =
  {
      println(s"\nGrading Exercise ${exercise}\n")
      var points = 10

      try{

        // Grab the submission, might throw an exception
        val sub = p.parseDFA(s"data/submission/${exercise}")

        // Handle a correct submission, might throw an exception
        if ( sub.equals(sol) ) {
           println( s"${exercise} passed evaluation" )
        } // if
        else{
          println(s"Your submission: \n${sub}")
          val excess_machine = sub.intersect(sol.complement()).minimize()
          val missed_machine = sol.intersect(sub.complement()).minimize()
          //handle the case where the student submitted a machine which
          //accepts strings that it shouldn't
          if ( !( excess_machine.recognizesEmptyLanguage() )) {
            println(s"-5 points.\n"                                    +
                    s"Your submission accepted some strings that it "  +
                    s"shouldn't have accepted.\n"                      +
                    s"This machine accepts those excessive strings.\n" +
                    s"${excess_machine}")
            points -= 5
          } // if
          //handle the case where the student submitted a machine which
          //didn't accept all of the strings that it should have
          if ( !( missed_machine.recognizesEmptyLanguage() )) {
            println(s"-5 points\n"                                           +
                    s"Your submission did not accept all the strings that" +
                    s"it should have.\n "                                  +
                    s"The following machine recognizes those strings: \n"  +
                    s"${missed_machine}")
            points -= 5
          }
        } // else
      }catch{
        case pe : ParserException => {println(s"\n${pe}\n");
                                      points = 0}
        case nse : NoSubmissionException => {println(s"\n${nse}\n");
                                             points = 0}
        case me : MachineException => {println(s"\n${me}\n");
                                       points = 0}
      }
      return points
  } // compareDFAs

  val sscores = Map[String,scala.collection.immutable.Map[String,Int]]()
  val scores = Map[String,Int]()
  val p = new Parser()

  val machineDir = "data/solutions2/"

  //The solution to 1.4.a is the intersection of two simpler machines...
  val m14a1 = p.parseDFA(machineDir + "1.4a1")
  val m14a2 = p.parseDFA(machineDir + "1.4a2")
  val m14a = m14a1.intersect(m14a2)

  val m14c = p.parseDFA(machineDir + "1.4c")

  //The solution to 1.5.c is the complement of a simpler machine...
  val m15c = p.parseDFA(machineDir + "1.5c").complement()

  /* The solution to 1.5.d is the complement of a machine which is *
   * far easier to write as an NFA than a DFA                      */
  val m15d = p.parseNFA(machineDir + "1.5d").complement().DFAify()

  scores += "1.4.a" -> compareDFAs(m14a,"1.4a")
  scores += "1.4.c" -> compareDFAs(m14c,"1.4c")
  scores += "1.5.c" -> compareDFAs(m15c,"1.5c")
  scores += "1.5.d" -> compareDFAs(m15d,"1.5d")

  implicit val formats = net.liftweb.json.DefaultFormats
  sscores += "scores" -> scores.toMap
  println(compact(render(decompose(sscores.toMap))))
} // SampleGrader
