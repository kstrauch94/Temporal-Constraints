#theory untimed_c {
untimed_term {-.  : 0, unary;
	      +.  : 0, unary;
	      -~ : 0, unary;
	      +~ : 0, unary};

sig_term {--  : 0, unary;
	      ++  : 0, unary};

&constraint/3 :  untimed_term, head;
&constraint/2 :  untimed_term, head;

&signature/0 : sig_term, any
}.


