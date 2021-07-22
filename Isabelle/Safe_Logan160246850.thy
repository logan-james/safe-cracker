theory Safe_Logan160246850
  imports VDMToolkit
begin 
section \<open> Intro  \<close>

text\<open>  
  Student name: Logan Turner
  Student number: 160246850
  Institution: Newcastle University

  This file is a (rudimentary) Isabelle translation of my Safe Cracker VDMSL file.

  There are functions missing - namely, post-conditions for functions as well as proofs.
  There are also many errors where syntax is incorrect or a function has just not been
  well defined.
\<close>
(**********************************************************)
section \<open> Imports \<close>

text\<open> 
  \begin{vdmsl}[breaklines=true]

  module SafeCrackerStd
  imports from IO		 operations  println	renamed println;
                                printf  renamed printf;
                                print		renamed print;
                                
  exports all
  definitions
 
  \end{vdmsl}
\<close>
(**********************************************************)
section \<open> VDM Values \<close>

text\<open> 
\begin{vdmsl}[breaklines=true]

values

	MAX_WHEELS: nat1 = 4;
	SECRET_SUM: nat1 = 40;
	WHEEL_LENGTH: nat1 = 16;

\end{vdmsl}
\<close>

abbreviation
  MAX_WHEELS :: VDMNat1 where "MAX_WHEELS \<equiv> 20"
abbreviation
  SECRET_SUM :: VDMNat1 where "SECRET_SUM \<equiv> 40"
abbreviation
  WHEEL_LENGTH :: VDMNat1 where "WHEEL_LENGTH \<equiv> 16"

definition
  inv_MAX_WHEELS :: "\<bool>"
where
  "inv_MAX_WHEELS \<equiv> inv_VDMNat1 MAX_WHEELS"

definition 
  inv_SECRET_SUM :: "\<bool>"
  where
"inv_SECRET_SUM \<equiv> inv_VDMNat1 SECRET_SUM"

definition
  inv_WHEEL_LENGTH :: "\<bool>"
  where
"inv_WHEEL_LENGTH \<equiv> inv_VDMNat1 SECRET_SUM"

(*--------------------------------------------*)
subsection \<open> Values - Test Safe \<close>

text\<open>
\begin{vdmsl}[breaklines=true]

values 

	SAFE_WITH_SOLUTION: Safe =
	mk_Safe
	( 
		[
			mk_Wheel([6, <Empty>, 13, <Empty>, 3, <Empty>, 3, <Empty>, 6, <Empty>, 10, <Empty>, 10, <Empty>, 10, <Empty>], 
								[<Empty>, <Empty>, <Empty>, <Empty>, <Empty>, <Empty>, <Empty>, <Empty>, <Empty>, <Empty>, <Empty>, <Empty>, <Empty>, <Empty>, <Empty>, <Empty>]),
			mk_Wheel([10, <Empty>, 2, <Empty>, 22, <Empty>, 2, <Empty>, 17, <Empty>, 15, <Empty>, 14, <Empty>, 5, <Empty>], 
								[1, 6, 10, 6, 10, 2, 6, 10, 4, 1, 5, 5, 4, 8, 6, 3]),
			mk_Wheel([16, <Empty>, 17, <Empty>, 2, <Empty>, 2, <Empty>, 10, <Empty>, 15, <Empty>, 6, <Empty>, 9, <Empty>],
								[11, 27, 14, 5, 5, 7, 8, 24, 8, 3, 6, 15, 22, 6, 1, 1]), 
			mk_Wheel(	[2, 15, 23, 19, 3, 2, 3, 27, 20, 11, 27, 10, 19, 10, 13, 10], 
								[22, 9, 5, 10, 5, 1, 24, 2, 10, 9, 7, 3, 12, 24, 10, 9])
		],
		[0,0,0]
	);
	
\end{vdmsl}
\<close>

value "wheel1 \<lparr> outer = [6, Empty, 13, Empty, 3, Empty, 3, Empty, 6, Empty, 10, Empty, 10, Empty, 10, Empty],
                inner = [Empty, Empty, Empty, Empty, Empty, Empty, Empty, Empty, Empty, Empty, Empty, Empty, Empty, Empty, Empty, Empty]
              \<rparr>"
value "wheel2 \<lparr> outer = [10, Empty, 2, Empty, 22, Empty, 2, Empty, 17, Empty, 15, Empty, 14, Empty, 5, Empty],
                inner = [1, 6, 10, 6, 10, 2, 6, 10, 4, 1, 5, 5, 4, 8, 6, 3]
              \<rparr>"
value "wheel3 \<lparr> outer = [16, Empty, 17, Empty, 2, Empty, 2, Empty, 10, Empty, 15, Empty, 6, Empty, 9, Empty],
                inner = [11, 27, 14, 5, 5, 7, 8, 24, 8, 3, 6, 15, 22, 6, 1, 1]
              \<rparr>"
value "wheel4 \<lparr> outer = 	[2, 15, 23, 19, 3, 2, 3, 27, 20, 11, 27, 10, 19, 10, 13, 10],
                inner = [22, 9, 5, 10, 5, 1, 24, 2, 10, 9, 7, 3, 12, 24, 10, 9]
              \<rparr>"

abbreviation
  SAFE_WITH_SOLUTION :: Safe
  where 
  "SAFE_WITH_SOLUTION \<equiv> \<lparr> wheels = (wheel1, wheel2, wheel3, wheel4), combinations = [0,0,0] \<rparr>"

definition
  inv_SAFE_WITH_SOLUTION :: "\<bool>"
where
  "inv_SAFE_WITH_SOLUTION \<equiv> inv_Safe0 SAFE_WITH_SOLUTION"

(*-- this is definitely incorrect - with more time i would fix this --*)
(*-- isabelle is unable to find the type 'Safe' which is defined further down --*)
(*-- and wheels are not defined correctly. basically, none of this part works, but is more of a starting point --*)

(********************************************************)
section \<open> VDM types \<close>

(*-----------------------------------------------------------*)
subsection \<open> Safe Components \<close>

text\<open>
\begin{vdmsl}[breaklines=true]

types 

	MaxValue = nat1
	inv v == v < SECRET_SUM - (MAX_WHEELS - 1);

	Value = MaxValue | Empty;
	
	ValueSequence = seq of Value
	inv s == len s = WHEEL_LENGTH;
	
	Rotation = nat
	inv r == r < WHEEL_LENGTH;
	
	Combination = seq of Rotation
	inv s == len s < MAX_WHEELS;

\end{vdmsl}
\<close>

(*-- values --*)

type_synonym MaxValue = "VDMNat1" 

definition
  inv_MaxValue :: "MaxValue \<Rightarrow> \<bool>" 
where
  "inv_MaxValue mv \<equiv> inv_VDMNat1 mv \<and> mv < (SECRET_SUM - (MAX_WHEELS - 1))"

datatype Value = "VDMNat1" | Empty

type_synonym ValueSequence = "MaxValue VDMSeq" 

definition
  inv_ValueSequence :: "ValueSequence \<Rightarrow> \<bool>" 
  where
  "inv_ValueSequence vs \<equiv> ((\<forall> i \<in> inds vs . inv_ValueSequence (vs $ i)) \<and> 
                           vdm_card (elems vs) = len vs)"

(*-- rotation --*)

type_synonym Rotation = "VDMNat"

definition
  inv_Rotation :: "Rotation \<Rightarrow> \<bool>" 
  where
"inv_Rotation r \<equiv> inv_VDMNat r \<and> r < WHEEL_LENGTH"

(*-- combination --*)

type_synonym Combination = "Rotation VDMSeq"

definition
  inv_Combination :: "Combination \<Rightarrow> \<bool>" 
  where
  "inv_Combination c \<equiv> \<forall> i \<in> inds c . inv_Combination (c $ i)" 

(* do some lemmas here ? *)

(*---------------------------------------------------------*)
subsection \<open> Wheels and the Safe \<close>

text\<open>
\begin{vdmsl}[breaklines=true]

	Wheel :: 
		outer : ValueSequence
		inner : ValueSequence;
	
	WheelSequence = seq of Wheel
	inv s == len s <= MAX_WHEELS and
	(len s = MAX_WHEELS => (
		(forall v in set elems s(len s).outer & v <> Empty) and
		(forall v in set elems (hd s).inner & v = Empty))
	);

\end{vdmsl}\<close>


record Wheel =
  outer :: ValueSequence
  inner :: ValueSequence
print_theorems

term outer
term inner 

(*-- set values here ? --*)

text\<open>Have to check the type invariants of each field in a record explicitly\<close>
definition
  inv_Wheel0 :: "Wheel \<Rightarrow> \<bool>"
  where
  "inv_Wheel0 w \<equiv> (inv_ValueSequence (outer w) \<and>
                 inv_ValueSequence (inner w) \<and> True)"

type_synonym WheelSequence = "Wheel VDMSeq"

definition 
  inv_WheelSequence :: "WheelSequence \<Rightarrow> \<bool>" 
  where
  "inv_WheelSequence ws \<equiv> (\<forall> i \<in> inds ws . inv_WheelSequence (ws $ i)) \<and>
                (
                  len ws = MAX_WHEELS \<longrightarrow>
                  (\<forall> v \<in> elems ws(len ws).outer & v \<noteq> Empty) \<and>
                  (\<forall> v \<in> elems (hd ws).inner & v \<equiv> Empty)
                )"

text\<open>
\begin{vdmsl}[breaklines=true]

	Safe ::
		wheels : WheelSequence
		combination : Combination
	inv s == len s.wheels = len s.combination + 1;

\end{vdmsl}\<close>

record Safe = 
  wheels :: WheelSequence
  combination :: Combination
print_theorems

term wheels
term combination

(*-- set values here ? --*)

text\<open>Have to check the type invariants of each field in a record explicitly\<close>
definition
  inv_Safe0 :: "Safe \<Rightarrow> \<bool>"
  where
  "inv_Safe0 s \<equiv> (inv_WheelSequence (wheels s) \<and>
                 inv_Combination (combination s) \<and> True) \<and>
                  (len s.wheels \<equiv> len s.combination + 1)"


text\<open>
\begin{vdmsl}[breaklines=true]

	ValidSafe = Safe
	inv s == exists_combination([], s);

\end{vdmsl}\<close>


type_synonym ValidSafe = "Safe" 

definition
  inv_ValidSafe :: "ValidSafe \<Rightarrow> \<bool>" 
where
  "inv_ValidSafe vs \<equiv> inv_Safe0 vs \<and>  exists_combination([], vs)"


(**********************************************************)
section \<open> VDM Functions \<close>

text\<open>
  This section covers the functions written in VDM
\<close>

(*-------------------------------------------------------*)
subsection \<open> function: exists_combination \<close>

text\<open>
\begin{vdmsl}[breaklines=true]

	exists_combination: seq of Rotation * Safe -> bool
  exists_combination(prev, s) ==
      if len prev = len s.combination 
      then check_combination(mk_Safe(s.wheels, prev))
      else
      	exists x in set {0,...,WHEEL_LENGTH - 1} & exists_combination(prev ^ [x], s)
      measure len s.combination - len prev
  ;

\end{vdmsl}\<close>

definition
  exists_combination :: "Rotation VDMSeq \<Rightarrow> Safe"
  where
  "exists_combination prev s \<equiv>
    if (len prev) = len (combination s)
    then check_combination(\<lparr> wheels = (wheels s), combination = prev \<rparr>)
    else
      \<exists> x \<in> {0,\<dots>,WHEEL_LENGTH-1} & exists_combination(prev ^ [x], s)
    measure len s.combination - len prev
"

(*-- i know the above is completely incorrect and not how recursion is handled in isabelle --*)
(*-- with more time i would like to do this correctly --*)

(*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
subsubsection \<open> Specification \<close>

definition
  pre_exists_combination :: "Rotation VDMSeq \<Rightarrow> Safe"
  where
  "pre_exists_combination \<equiv> inv_Rotation \<and> inv_Safe0 \<and> inv_Combination"

(*-------------------------------------------------------*)
subsection \<open> function: crack the safe \<close>

text\<open>
\begin{vdmsl}[breaklines=true]

  crack_safe: seq of Rotation * ValidSafe -> seq of Rotation
  crack_safe(prev,s) ==
      if len prev = len s.combination 
      then prev
      else
          crack_safe(prev ^ [(iota x in set {0,...,WHEEL_LENGTH - 1} & exists_combination(prev ^ [x], s))], s)
      measure len s.combination - len prev
  ;

\end{vdmsl}\<close>

definition
  crack_safe :: "ValidSafe \<Rightarrow> Combination"
  where
  "crack_safe prev s \<equiv>
    
    if (len prev) = (len (combination s))
    then prev
    else
      crack_safe
      (
        prev ^ [(iota x \<in> {0,...,WHEEL_LENGTH - 1} & exists_combination(prev ^ [x], s))]
        , s
      )
      measure len (combination s) - len prev" 

(*-- i know the above is completely incorrect and not how recursion or iota is handled in isabelle --*)
(*-- with more time i would like to do this correctly --*)

(*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
subsubsection \<open> Specification \<close>

definition
  pre_crack_safe :: "ValidSafe \<Rightarrow> Combination" 
  where
  "pre_crack_safe \<equiv> inv_ValidSafe \<and> inv_Safe0 \<and> inv_Combination \<and> inv_Rotation"

(*-------------------------------------------------------*)
subsection \<open> function: check combination \<close>

text\<open>
\begin{vdmsl}[breaklines=true]

	check_combination: Safe -> bool
	check_combination(s) ==
		forall i in set {0,...,WHEEL_LENGTH - 1} & add_column(s, i) = SECRET_SUM
	;

\end{vdmsl}\<close>

definition
  check_combination :: "Safe \<Rightarrow> \<bool>"
  where
   "check_combination Safe \<equiv>  \<forall> i \<in> {0, \<dots>, WHEEL_LENGTH - 1} & add_column(s, i) \<equiv> SECRET_SUM"

(*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
subsubsection \<open> Specification \<close>

definition 
  pre_check_combination :: "Safe \<Rightarrow> \<bool>"
where
  "pre_check_combination \<equiv> inv_Safe0"

text \<open> Make sure the invariant for Safe holds before trying to execute this method \<close>


(*-------------------------------------------------------*)
subsection \<open> functions: inner_add \<close>

text\<open>
  Adding numbers in a column together is quite involved --
     its been split into two functions, 'inner_add' and 'add_column'.
  add_column makes use of inner_add. Here, inner_add will be defined first, followed by 
  add_column. 

  inner_add is complex in that its recursive
\<close>

text\<open>
\begin{vdmsl}[breaklines=true]

	inner_add: Safe * nat -> nat
	inner_add(s, col_num) ==
	let pos = [((col_num + hd s.combination) mod WHEEL_LENGTH) + 1, if len s.combination > 1 then ((col_num + hd tl s.combination) mod WHEEL_LENGTH) + 1 else col_num + 1] in
		if len s.wheels > 2
		then 
			(if (hd s.wheels).outer(pos(1)) = Empty
			then (hd tl s.wheels).inner(pos(2))
			else (hd s.wheels).outer(pos(1)))
			+
			inner_add(mk_Safe(tl s.wheels, tl s.combination), col_num)
		else
		(
			(if (hd s.wheels).outer(pos(1)) = Empty
			then (hd tl s.wheels).inner(pos(2))
			else (hd s.wheels).outer(pos(1)))
		)
	pre col_num < WHEEL_LENGTH and len s.wheels >= 2
	measure len s.wheels
	;

\end{vdmsl}\<close>

definition
  inner_add :: "Safe \<Rightarrow> VDMNat \<Rightarrow> VDMNat"
  where 
  "inner_add s col_num \<equiv>
  
    let pos = [((col_num + hd s.combination) mod WHEEL_LENGTH) + 1, 
      if len s.combination > 1 
      then ((col_num + hd tl s.combination) mod WHEEL_LENGTH) + 1
      else col_num + 1] in
(
  if len s.wheels > 2
  then
    (
      if (outer (hd (wheels s)))(pos 0) \<equiv> Empty
      then (hd tl (wheels s)).inner(pos 1)
      else (hd (wheels s)).outer(pos 0)
    )
    +
			inner_add(\<lparr>wheels = tl s.wheels, combination = tl s.combination\<rparr>, col_num)
		else
		(
			(
        if (hd (wheels s)).outer(pos 0) \<equiv> Empty
        then (hd tl (wheels s)).inner(pos 1)
        else (hd (wheels s)).outer(pos 0)
      )
		)
)"


(*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
subsubsection \<open> Specification \<close>

definition 
  pre_inner_add :: "Safe \<Rightarrow> VDMNat \<Rightarrow> VDMNat"
where
  "pre_inner_add s col_num \<equiv> 
    inv_Safe0 s \<and> 
    col_num < WHEEL_LENGTH \<and> 
    len (s wheels) \<ge> 2"

text \<open> Make sure the invariant for Safe holds, as well as the pre conditions \<close>


(*-------------------------------------------------------*)
subsection \<open> functions: add_column \<close>

text\<open>
  Adding numbers in a column together is quite involved --
     its been split into two functions, 'inner_add' and 'add_column'.
  
  Add_column makes use of inner_add
\<close>

text\<open>
\begin{vdmsl}[breaklines=true]

	add_column: Safe * nat -> nat
	add_column(s, col_num) ==
		s.wheels(len s.wheels).outer(col_num + 1) + inner_add(s, col_num)
	;

\end{vdmsl}\<close>

definition
  add_column :: "Safe \<Rightarrow> VDMNat \<Rightarrow> VDMNat" 
  where
  "add_column s col_num \<equiv>
    (outer (wheels(len (wheels s)) s))(col_num + 1)
    + inner_add(s, col_num)"

(*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
subsubsection \<open> Specification \<close>

definition 
  pre_add_column :: "Safe \<Rightarrow> VDMNat \<Rightarrow> VDMNat"
where
  "pre_add_column s col_num \<equiv> 
    inv_Safe0 s \<and> 
    col_num < WHEEL_LENGTH"

text \<open> Make sure the invariant for Safe holds, as well as the column number being
smaller than the WHEEL_LENGTH \<close>


end