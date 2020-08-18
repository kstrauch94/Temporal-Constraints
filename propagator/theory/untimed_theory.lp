#theory untimed_c {
untimed_term {-.  : 0, unary;
	      +.  : 0, unary;
	      -~ : 0, unary;
	      +~ : 0, unary};

time_term { + : 0, unary;
	    - : 0, unary};

&constraint/0 :  untimed_term, body;
&time/0 : time_term, head
}.


