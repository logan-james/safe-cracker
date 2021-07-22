theory VDMTypes
imports VDMToolkit
begin

(*********************************************************************************)
section \<open>Constants\<close>

text \<open>MAX is a reserved word in Isabelle,
values
	MAX: nat1 = 10;
\<close>
abbreviation
  LMAX :: "VDMNat1"
where
  "LMAX \<equiv> 10"

definition
  inv_LMAX :: "\<bool>"
  where
  "inv_LMAX \<equiv> inv_VDMNat1 LMAX"

(*********************************************************************************)
section \<open>Numeric types\<close>

text \<open>MyType = nat1 inv n == n <= LMAX"\<close>

type_synonym MyType = VDMNat1

definition
  inv_MyType :: "VDMNat1 \<Rightarrow> \<bool>"
  where
  "inv_MyType n \<equiv> 
    inv_VDMNat1 n 
  \<and> n \<le> LMAX"

text \<open>VDM ranges {1,...,10} can be represented as below. Isabelle also has open/closed ranges\<close>
value "{1..(10::nat)}"
value "{1..<(10::nat)}"
value "{1<..<(10::nat)}"

value "inv_MyType(0)"
value "inv_MyType(5)"
value "inv_MyType(10)"

(*********************************************************************************)
section \<open>Set types\<close>

text \<open>MySet = set of MyType inv s == s <> {};\<close>

type_synonym MySet0 = "VDMNat1 VDMSet"
  
definition
  inv_MySet0 :: "VDMNat1 VDMSet \<Rightarrow> \<bool>"
  where
  "inv_MySet0 s \<equiv> 
      inv_VDMSet s \<and> 
      (\<forall> e . e \<in> s \<longrightarrow> e \<ge> 0 \<and> e \<le> LMAX) \<and>
      s \<noteq> {}"

type_synonym MySet = "MyType VDMSet"
  
definition
  inv_MySet :: "MyType VDMSet \<Rightarrow> \<bool>"
  where
  "inv_MySet s \<equiv> inv_VDMSet s \<and> 
                 inv_SetElems inv_MyType s \<and> 
                 s \<noteq> {}"

value "inv_SetElems inv_MyType {1,2,3}"

value "inv_MySet {1,2,(3::MyType)}"

lemma "inv_MySet {1,2,3}"
  unfolding inv_MySet_def 
  unfolding          inv_SetElems_def 
          unfolding  inv_MyType_def 
           unfolding inv_VDMNat1_def 
           unfolding inv_VDMSet_def
  by simp

lemma "\<not> inv_MySet {1,2,20}"
  unfolding inv_MySet_def 
            inv_SetElems_def 
            inv_MyType_def 
            inv_VDMNat1_def 
            inv_VDMSet_def
  by simp

lemma "inv_MySet s" 
  unfolding inv_MySet_def 
            inv_SetElems_def 
            inv_MyType_def 
            inv_VDMNat1_def 
            inv_VDMSet_def
  oops
            
definition
  inv_MySetExplicit :: "MyType VDMSet \<Rightarrow> \<bool>"
  where
  "inv_MySetExplicit s \<equiv> 
                 finite s \<and> 
                 (\<forall> e \<in> s . e > 0 \<and> e \<le> LMAX) \<and>
                 s \<noteq> {}"

lemma "inv_MySetExplicit s = inv_MySet s"
  unfolding  inv_MySetExplicit_def inv_MySet_def
inv_SetElems_def 
            inv_MyType_def 
            inv_VDMNat1_def 
            inv_VDMSet_def 
  apply auto
  done (* found typo "e \<ge> 0", fixed e > 0! Better not be explicit *)
  
text \<open>MySet1 = set1 of MyType\<close>

type_synonym MySet1 = "VDMNat1 VDMSet1"
  
definition
  inv_MySet1 :: "MyType VDMSet1 \<Rightarrow> \<bool>"
  where
  "inv_MySet1 s \<equiv> inv_VDMSet1 s \<and> 
                  inv_SetElems inv_MyType s"

lemma "inv_MySet1 s = inv_MySet s"
  unfolding  inv_MySet1_def inv_MySet_def
inv_SetElems_def 
            inv_MyType_def 
            inv_VDMNat1_def 
            inv_VDMSet_def 
            inv_VDMSet1_def
  by auto 

(*********************************************************************************)
section \<open>Seq types\<close>

type_synonym MySeq0 = "VDMNat1 VDMSeq"

definition
  inv_MySeq0 :: "VDMNat1 VDMSeq \<Rightarrow> \<bool>"
  where
  "inv_MySeq0 s \<equiv> (\<forall> i \<in> inds s . s $ i \<le> LMAX) \<and>
                  (\<forall> e \<in> elems s . e \<le> LMAX) \<and> 
                  vdm_card (elems s) = len s"

text\<open>MySeq = seq of MyType inv s == card elems s = len s;\<close>
type_synonym MySeq = "MyType VDMSeq"

definition
  inv_MySeq :: "MyType VDMSeq \<Rightarrow> \<bool>"
  where
  "inv_MySeq s \<equiv> inv_SeqElems inv_MyType s \<and> 
                  vdm_card (elems s) = len s"

value "inv_MySeq [1, 2, 3]"

lemma "inv_MySeq [1,2,3]"
  unfolding inv_MySeq_def
  inv_SeqElems_def inv_MyType_def inv_VDMNat1_def elems_def len_def vdm_card_def inv_VDMSet_def
  by simp

lemma "\<not> inv_MySeq [1,1,3]"
  unfolding inv_MySeq_def
  inv_SeqElems_def inv_MyType_def inv_VDMNat1_def elems_def len_def vdm_card_def inv_VDMSet_def
  by simp

type_synonym MySeqSeq0 = "MyType VDMSeq VDMSeq"

definition
  inv_MySeqSeq0 :: "MyType VDMSeq VDMSeq \<Rightarrow> \<bool>"
  where
  "inv_MySeqSeq0 ss \<equiv> 
    inv_SeqElems (inv_SeqElems inv_MyType) ss"

type_synonym MySeqX = "MyType VDMSeq"

definition
  inv_MySeqX :: "MyType  VDMSeq \<Rightarrow> \<bool>"
  where
  "inv_MySeqX s \<equiv> 
    inv_SeqElems inv_MyType s"

type_synonym MySeqSeq = "MyType VDMSeq VDMSeq"

definition
  inv_MySeqSeq :: "MyType VDMSeq VDMSeq \<Rightarrow> \<bool>"
  where
  "inv_MySeqSeq ss \<equiv> 
    inv_SeqElems inv_MySeqX ss"

(*********************************************************************************)
section \<open>Enum types\<close>

text\<open>Enum = <E1> | <E2>; \<close>

datatype Enum = E1 | E2  

find_theorems name:"VDMTypes.Enum"

text \<open>Even when no invariant exists, it's good idea to define it in case one arises later\<close>
definition
  inv_Enum :: "Enum \<Rightarrow> \<bool>"
  where
  "inv_Enum e \<equiv> True"
  
(*********************************************************************************)
section \<open>Map types\<close>

text\<open>MyMap = map MyType to (nat1 * Enum) inv m == dom m subset {LMAX div 2,...,LMAX}<E1> | <E2>; \<close>

(* TODO: add differences between each type in English! *)

type_synonym MyMap = "MyType \<rightharpoonup> (VDMNat \<times> Enum) VDMSet"
typ MyMap

value "[ 5 \<mapsto> {(0, E1)} ]::MyMap"

text 
\<open>Be very careful with div and mod. Their meaning is different in VDM and Isabelle when 
 dealing with negative numbers. Have a look inside VDMToolkit for details/examples. If both
 left and right sides of div/mod are >= 0, then you are fine. Otherwise, you will have harder 
 proofs to do. That means, make sure your invariants contain this if div/mod is used. In the case
 below, this is implicitly obvious given LMAX is 10 and both 10 and 2 are bigger than 0.\<close>

definition
  inv_MyMapRanElem :: "(MyType \<times> Enum) \<Rightarrow> \<bool>"
  where
  "inv_MyMapRanElem v \<equiv> 
    let (n, e) = v in 
      inv_MyType n \<and> inv_Enum e"

definition
  inv_MyMapRan :: "(MyType \<times> Enum) VDMSet \<Rightarrow> \<bool>"
  where
  "inv_MyMapRan s \<equiv>  inv_SetElems inv_MyMapRanElem s"

definition
  inv_MyMap :: "MyMap \<Rightarrow> \<bool>"
where
  "inv_MyMap m \<equiv> 
      inv_Map inv_MyType inv_MyMapRan m \<and>
      dom m \<subseteq> {LMAX vdmdiv 2 .. LMAX}"

lemma "inv_MyMap m" 
  unfolding inv_MyMap_def
 unfolding     inv_Map_def
  unfolding inv_MyMapRan_def inv_MyMapRanElem_def 
 unfolding     inv_MyType_def
  unfolding    inv_VDMNat1_def
 unfolding     inv_Enum_def 
 unfolding     inv_SetElems_def
 unfolding     inv_VDMSet_def
  apply simp
  apply safe
  oops

type_synonym MyMapOld = "MyType \<rightharpoonup> Enum"

definition
  inv_MyMapOld :: "MyMapOld \<Rightarrow> \<bool>"
where
  "inv_MyMapOld m \<equiv> 
      inv_Map inv_MyType inv_Enum m \<and>
      dom m \<subseteq> {LMAX vdmdiv 2 .. LMAX}"

text\<open>Map enumeration { 3 |-> <E1>, 2 |-> <E1>, 1 |-> <E2>, 4 |-> <E2> }\<close>

value
 "[ (3::MyType) |-> E1, 
              2 \<mapsto> E1, 
              1 \<mapsto> E2, 
              4 \<mapsto> E2]
 " 

value 
 "dom 
  [ (3::MyType) \<mapsto> E1, 
              2 \<mapsto> E1, 
              1 \<mapsto> E2, 
              4 \<mapsto> E2] 
 " 

lemma 
 "dom 
  [ (3::MyType) \<mapsto> E1, 
              2 \<mapsto> E1, 
              1 \<mapsto> E2, 
              4 \<mapsto> E2] 
  = {1..4}
 " 
  apply simp
  by auto

abbreviation
  mymap_test :: "MyType \<rightharpoonup> Enum"
  where
  "mymap_test \<equiv>  
  [ (3::MyType) \<mapsto> E1, 
              2 \<mapsto> E1, 
              1 \<mapsto> E2, 
              4 \<mapsto> E2]" 
lemma 
 "ran mymap_test = {E1, E2}"
  apply simp
  by auto

text\<open>Map applicaiton (the operator) + values outside domain\<close>

value "mymap_test 1"
value "mymap_test 2"
value "mymap_test 3"
value "mymap_test 4"
value "mymap_test 5"
value "mymap_test 565454235"
value "mymap_test 10"

value "mymap_test 1 = E2"
value "mymap_test 1 = Some E2"
value "the (mymap_test 1) = E2"
value "the (mymap_test 3) = E1"
value "the (mymap_test 5)"
value "mymap_test 5 = None"
value "5 \<notin> dom mymap_test"

text \<open>Map update\<close>

value "mymap_test(3 \<mapsto> E2) 3"
value "(mymap_test(3 \<mapsto> E2)) 3 = Some E2"
value "the((mymap_test(3 \<mapsto> E2)) 3) = E2"

lemma "dom Map.empty = {}" by simp

(*********************************************************************************)
section \<open>Record types\<close>

text\<open>
  MyRec ::
		x: MyType
		s: MySet
		l: MySeq
		m: MyMap
	inv mk_MyRec(x,s,l,m) ==
		x in set dom m inter elems l inter s
		and
		x in set dom m and x in set elems l and x in set s;
\<close>

text \<open>Record fields declare projection functions from record to field type\<close>
record MyRec =
  xfield :: MyType
  sfield :: MySet
  lfield :: MySeq
  mfield :: MyMap  
print_theorems

term xfield
term sfield
term lfield

value "(|xfield = 5, sfield = {5}, lfield = [5], mfield = [ 5 |-> {(0,E1)} ]|)"
value "\<lparr>xfield = 5, sfield = {5}, lfield = [5], mfield = [ 5 \<mapsto> {(0,E1)} ]\<rparr>"
value "xfield \<lparr>xfield = 3, sfield = {3}, lfield = [3], mfield = Map.empty\<rparr> = 3"
value "lfield \<lparr>xfield = 3, sfield = {3}, lfield = [3], mfield = Map.empty\<rparr> = [3]"

text\<open>Have to check the type invariants of each field explicitly\<close>
definition
  inv_MyRec0 :: "MyRec \<Rightarrow> \<bool>"
  where
  "inv_MyRec0 r \<equiv> inv_MyType (xfield r) \<and>
                 inv_MySet (sfield r) \<and>
                 inv_MySeq (lfield r) \<and>
                 inv_MyMap (mfield r) \<and> True"

value "inv_MyRec0 \<lparr>xfield = 3, sfield = {3}, lfield = [3], mfield = Map.empty\<rparr>"

lemma "inv_MyRec0 \<lparr>xfield = 3, sfield = {3}, lfield = [3], mfield = Map.empty\<rparr>" 
  unfolding inv_MyRec0_def
        inv_MyMap_def
        inv_MySeq_def
        inv_MySet_def
        inv_SeqElems_def
        inv_SetElems_def
        inv_Map_def
        inv_MyType_def
        inv_VDMSet_def
        inv_VDMNat1_def
  by simp 
    
definition
  inv_MyRec :: "MyRec \<Rightarrow> \<bool>"
  where
  "inv_MyRec r \<equiv> (let x=(xfield r); s=(sfield r); l=(lfield r); m=(mfield r) in  
                      inv_MyType x \<and>
                     inv_MySet s \<and>
                     inv_MySeq l \<and>
                     inv_MyMap m \<and> 
                     x \<in> (dom m) \<inter> (elems l) \<inter> s  
                     \<and>
                     x \<in> (dom m) \<and> x \<in> (elems l) \<and> x \<in> s)"

lemma "(let r=\<lparr>xfield = 3, sfield = {3}, lfield = [3], mfield = [3 \<mapsto> {(0,E1)}]\<rparr>;
            x=(xfield r); s=(sfield r); l=(lfield r); m=(mfield r) in x \<in> (dom m) \<inter> (elems l) \<inter> s)"
  by simp

lemma "inv_MyRec \<lparr>xfield = 3, sfield = {3}, lfield = [3], mfield = [3 \<mapsto> {(1,E1)}]\<rparr>" 
  unfolding inv_MyRec_def Let_def
  apply (simp,safe)
  unfolding inv_MyType_def inv_VDMNat1_def
     apply simp
  unfolding inv_MySet_def inv_VDMSet_def
    apply (simp add: inv_MyType_def inv_VDMNat1_def)
  unfolding inv_MySeq_def vdm_card_def elems_def inv_VDMSet_def
   apply simp
  apply (simp add: inv_MyType_def inv_VDMNat1_def l_inv_SeqElems_Cons)
  unfolding        inv_MyMap_def
  unfolding inv_MyMapRan_def inv_MyMapRanElem_def 
  apply safe
   apply (simp add: inv_Enum_def inv_Map_def inv_MyType_def inv_VDMNat1_def)
  apply simp
  oops
  
lemma "inv_MyRec \<lparr>xfield = 5, sfield = {5}, lfield = [5], mfield = [5 \<mapsto> {(1,E1)}]\<rparr>" 
  unfolding inv_MyRec_def
        inv_MyMap_def
        inv_MySeq_def
        inv_MySet_def
        inv_SeqElems_def
        inv_SetElems_def
        inv_MyType_def
        inv_VDMSet_def
        inv_VDMNat1_def
        inv_Enum_def
        inv_Map_def
        Let_def
        inv_MyMapRan_def
        inv_MyMapRanElem_def
  by simp_all
    
lemma "inv_MyRec r" 
  unfolding inv_MyRec_def Let_def
 unfolding       inv_MyMap_def
        inv_MyMapRan_def
        inv_MyMapRanElem_def
        inv_Map_def
 unfolding       inv_MySeq_def
  unfolding       inv_MySet_def
 unfolding       inv_SeqElems_def
 unfolding       inv_SetElems_def
 unfolding      inv_MyType_def
 unfolding       inv_VDMSet_def
  unfolding      inv_VDMNat1_def
  unfolding inv_Enum_def
  apply simp
  oops

(*********************************************************************************)
section \<open>Union types\<close>

text\<open>MyUnion = MyRec | MyMap; \<close>

datatype MyUnion = R MyRec | M MyMap  

definition
  inv_MyUnion :: "MyUnion \<Rightarrow> \<bool>"
  where
  "inv_MyUnion u \<equiv> 
    case u of
      R r \<Rightarrow> inv_MyRec r
    | M m \<Rightarrow> inv_MyMap m"

(*****************************************************************)  
section \<open> Some useful examples of various expressions \<close>

subsection \<open> Set translations: enumeration, comprehension, ranges \<close>

text \<open>Set comprehension\<close>

(* { expr | var . filter }, { var \<in> type . filter }, { var . filter } *)

value "{ x+x | x . x \<in> {(1::nat),2,3,4,5,6} }"
value "{ x+x | x . x \<in> {(1::nat),2,3} }"
value "{ x+x | x . x \<in> {(1::nat)..3} }" (* "not always work"*)
value "{ x*x | x . x \<in> {(1::int),2,3,5} }"


value "{0..(2::int)}"  
value "{0..<(3::int)}"  
value "{0<..<(3::int)}"  

subsection \<open> Seq translations: enumeration, comprehension, ranges \<close>

(* List application (i.e. s(x)) is available in Isabelle, but is zero based *)
value "[A, B, C] ! 0"
value "[A, B, C] ! 1"
value "[A, B, C] ! 2"
value "[A, B, C] ! 3"
value "nth [A, B, C] 0"

value "applyVDMSeq [A, B] 0" \<comment> \<open>out of range\<close>
value "applyVDMSeq [A, B] 1"
value "applyVDMSeq [A, B] 2"
value "applyVDMSeq [A, B] 3" \<comment> \<open>out of range\<close>

value "[A,B,C,D] $ 0"  
value "[A,B,C,D] $ 1"
value "[A,B,C,D] $ 2"
value "[A,B,C,D] $ 3"
value "[A,B,C,D] $ 4"
value "[A,B,C,D] $ 5"

text \<open>Seq comprehension\<close>
  
value "{ [A,B,C] ! i | i . i \<in> {0,1,2} }"
value "{ [A,B,C,D,E,F] ! i | i . i \<in> {0,2,4} }"
(* { s(i) | i in set inds s & i mod 2 = 0 } *)

value "{ [A,B,C] ! i | i . i \<in> {0,1,2} }"
value "[ x . x \<leftarrow> [0,1,(2::int)]]" (*avoid if possible... *)
value "[ x . x \<leftarrow> [0 .. 3] ]"

value "len [A, B, C]"
value "elems [A, B, C, A, B]"
value "elems [(0::nat), 1, 2]"
value "inds [A,B,C]"
value "inds_as_nat [A,B,C]"
value "card (elems [10, 20, 30, 1, 2, 3, 4, (5::nat), 10])"
value "len [10, 20, 30, 1, 2, 3, 4, (5::nat), 10]"
 
text \<open>Map comprehension (almost)\<close>
  
text \<open> Enumeration through sequences (or sequence comprehension) \<close>
value "[ [(3::nat),4,5] [\<mapsto>] [(4::nat),5,6,7] ] = [3 \<mapsto> 4, 4 \<mapsto> 5, 5 \<mapsto> 6]"

lemma "[ [(3::nat),4,5] [\<mapsto>] [(4::nat),5,6,7] ] = [3 \<mapsto> 4, 4 \<mapsto> 5, 5 \<mapsto> 6]"
  by simp

lemma "[ [(3::nat),4,5] [\<mapsto>] [(4::nat)] ] = [3 \<mapsto> 4]" 
  by simp

lemma "[ [(3::nat),3,5] [\<mapsto>] [(4::nat),5,6,7] ] = [3 \<mapsto> 5, 5 \<mapsto> 6]"
  by simp

lemma "[[ x . x \<leftarrow> [0,1,(2::nat)] ] [\<mapsto>] [y . y \<leftarrow> [3,4,(5::nat)]] ] = [0 \<mapsto> 3, 1 \<mapsto> 4, 2 \<mapsto> 5]"
  by simp

end