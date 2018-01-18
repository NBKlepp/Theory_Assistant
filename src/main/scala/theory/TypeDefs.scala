package theory

object TypeDefs{
       type State           = String
       type Symbl	    = String
       type TransitionInput = (State,Symbl)
       type RegEx 	    = String
       //def NullState 	    = "-1"
       def NullState	    = "\u2205"
       //def epsilon 	    = "-1"
       def epsilon	    = "\u03B5"
       def p	  	    = "p"
       def Epsilon	    = '\u03B5'
       def Union	    = '\u222A'
       def NullRegEx	    = "\u2205"
       def NullStar	    = "(\u2205)*"

}

