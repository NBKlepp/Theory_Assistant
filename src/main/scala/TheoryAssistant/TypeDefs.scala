package TheoryAssistant

object TypeDefs{
       type State     = String
       type Symbl	    = String

       type RegEx 	   = String
       def NullState	    = "\u2205"
       def epsilon	    = "\u03B5"
       def p	  	    = "p"
       def Epsilon	    = '\u03B5'
       def Union	    = '\u222A'
       def NullRegEx	    = "\u2205"
       def NullStar	    = "(\u2205)*"
       def _DFA = 0
       def _NFA = 1
       def _PDA = 2
       def _TM  = 3
       type TransitionInput = (State,Symbl)
}
