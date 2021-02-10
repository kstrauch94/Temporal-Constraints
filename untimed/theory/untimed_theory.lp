#theory untimed_c {
untimed_term {-.  : 0, unary;
	      +.  : 0, unary;
	      -~ : 0, unary;
	      +~ : 0, unary};

sig_term {--  : 0, unary;
	      ++  : 0, unary};

&constraint/1 :  untimed_term, any;
&constraint/2 :  untimed_term, any;

&signature/0 : sig_term, any
}.


