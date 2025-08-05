From iris.proofmode Require Import base intro_patterns spec_patterns
                                   sel_patterns reduction
                                   string_ident.
From iris.proofmode Require Import classes notation.
From iris.prelude Require Import options.
Export ident.

From iris.proofmode Require Import ltac_tactics.
From iris_named_props Require Export named_props.

(* copy of proofmode/tokens.v *)
Inductive token :=
  | TName : string → token
  | TNat : nat → token
  | TAnon : token
  | TFrame : token
  | TBar : token
  | TBracketL : token
  | TBracketR : token
  | TAmp : token
  | TParenL : token
  | TParenR : token
  | TBraceL : token
  | TBraceR : token
  | TPure : option string → token
  | TIntuitionistic : token
  | TModal : token
  | TPureIntro : token
  | TIntuitionisticIntro : token
  | TModalIntro : token
  | TSimpl : token
  | TDone : token
  | TForall : token
  | TAll : token
  | TMinus : token
  | TSep : token
  | TArrow : direction → token
  (* new *)
  | TNamed : token.

Inductive state :=
  | SName : string → state
  | SNat : nat → state
  | SPure : string -> state
  | SNone : state.

Definition cons_state (kn : state) (k : list token) : list token :=
  match kn with
  | SNone => k
  | SName s => TName (String.rev s) :: k
  | SPure s => TPure (if String.eqb s "" then None else Some (String.rev s)) :: k
  | SNat n => TNat n :: k
  end.

Fixpoint tokenize_go (s : string) (k : list token) (kn : state) : list token :=
  match s with
  | "" => reverse (cons_state kn k)
  | String "?" s => tokenize_go s (TAnon :: cons_state kn k) SNone
  | String "$" s => tokenize_go s (TFrame :: cons_state kn k) SNone
  | String "[" s => tokenize_go s (TBracketL :: cons_state kn k) SNone
  | String "]" s => tokenize_go s (TBracketR :: cons_state kn k) SNone
  | String "|" s => tokenize_go s (TBar :: cons_state kn k) SNone
  | String "(" s => tokenize_go s (TParenL :: cons_state kn k) SNone
  | String ")" s => tokenize_go s (TParenR :: cons_state kn k) SNone
  | String "&" s => tokenize_go s (TAmp :: cons_state kn k) SNone
  | String "{" s => tokenize_go s (TBraceL :: cons_state kn k) SNone
  | String "}" s => tokenize_go s (TBraceR :: cons_state kn k) SNone
  | String "%" s => tokenize_go s (cons_state kn k) (SPure "")
  | String "#" s => tokenize_go s (TIntuitionistic :: cons_state kn k) SNone
  | String ">" s => tokenize_go s (TModal :: cons_state kn k) SNone
  | String "!" (String "%" s) => tokenize_go s (TPureIntro :: cons_state kn k) SNone
  | String "!" (String "#" s) => tokenize_go s (TIntuitionisticIntro :: cons_state kn k) SNone
  | String "!" (String ">" s) => tokenize_go s (TModalIntro :: cons_state kn k) SNone
  | String "/" (String "/" (String "=" s)) =>
     tokenize_go s (TSimpl :: TDone :: cons_state kn k) SNone
  | String "/" (String "/" s) => tokenize_go s (TDone :: cons_state kn k) SNone
  | String "/" (String "=" s) => tokenize_go s (TSimpl :: cons_state kn k) SNone
  | String "*" (String "*" s) => tokenize_go s (TAll :: cons_state kn k) SNone
  | String "*" s => tokenize_go s (TForall :: cons_state kn k) SNone
  | String "-" (String ">" s) => tokenize_go s (TArrow Right :: cons_state kn k) SNone
  | String "<" (String "-" s) => tokenize_go s (TArrow Left :: cons_state kn k) SNone
  | String "-" s => tokenize_go s (TMinus :: cons_state kn k) SNone
  | String (Ascii.Ascii false true false false false true true true) (* unicode ∗ *)
      (String (Ascii.Ascii false false false true false false false true)
      (String (Ascii.Ascii true true true false true false false true) s)) =>
     tokenize_go s (TSep :: cons_state kn k) SNone
  (* new *)
  | String "@" s => tokenize_go s (TNamed :: cons_state kn k) SNone
  | String a s =>
     (* TODO: Complain about invalid characters, to future-proof this
     against making more characters special. *)
     if Ascii.is_space a then tokenize_go s (cons_state kn k) SNone else
     match kn with
     | SNone =>
        match Ascii.is_nat a with
        | Some n => tokenize_go s k (SNat n)
        | None => tokenize_go s k (SName (String a ""))
        end
     | SName s' => tokenize_go s k (SName (String a s'))
     | SPure s' => tokenize_go s k (SPure (String a s'))
     | SNat n =>
        match Ascii.is_nat a with
        | Some n' => tokenize_go s k (SNat (n' + 10 * n))
        | None => tokenize_go s (TNat n :: k) (SName (String a ""))
        end
     end
  end.
Definition tokenize (s : string) : list token := tokenize_go s [] SNone.
(* end tokens.v *)

(* copy of proofmode/intro_patterns.v *)
Inductive intro_pat :=
  | IIdent : ident → intro_pat
  | IFresh : intro_pat
  | IDrop : intro_pat
  | IFrame : intro_pat
  | IList : list (list intro_pat) → intro_pat
  | IPure : gallina_ident → intro_pat
  | IIntuitionistic : intro_pat → intro_pat
  | ISpatial : intro_pat → intro_pat
  | IModalElim : intro_pat → intro_pat
  | IRewrite : direction → intro_pat
  | IPureIntro : intro_pat
  | IModalIntro : intro_pat
  | ISimpl : intro_pat
  | IDone : intro_pat
  | IForall : intro_pat
  | IAll : intro_pat
  | IClear : sel_pat → intro_pat
  | IClearFrame : sel_pat → intro_pat
  (* new *)
  | INamedPat : intro_pat.

Module intro_pat.
Inductive stack_item :=
  | StPat : intro_pat → stack_item
  | StList : stack_item
  | StConjList : stack_item
  | StBar : stack_item
  | StAmp : stack_item
  | StIntuitionistic : stack_item
  | StSpatial : stack_item
  | StModalElim : stack_item.
Notation stack := (list stack_item).

Fixpoint close_list (k : stack)
    (ps : list intro_pat) (pss : list (list intro_pat)) : option stack :=
  match k with
  | StList :: k => Some (StPat (IList (ps :: pss)) :: k)
  | StPat pat :: k => close_list k (pat :: ps) pss
  | StIntuitionistic :: k =>
     '(p,ps) ← maybe2 (::) ps; close_list k (IIntuitionistic p :: ps) pss
  | StModalElim :: k =>
     '(p,ps) ← maybe2 (::) ps; close_list k (IModalElim p :: ps) pss
  | StBar :: k => close_list k [] (ps :: pss)
  | _ => None
  end.

Fixpoint big_conj (ps : list intro_pat) : intro_pat :=
  match ps with
  | [] => IList [[]]
  | [p] => IList [[ p ]]
  | [p1;p2] => IList [[ p1 ; p2 ]]
  | p :: ps => IList [[ p ; big_conj ps ]]
  end.

Fixpoint close_conj_list (k : stack)
    (cur : option intro_pat) (ps : list intro_pat) : option stack :=
  match k with
  | StConjList :: k =>
     ps ← match cur with
          | None => guard (ps = []);; Some [] | Some p => Some (p :: ps)
          end;
     Some (StPat (big_conj ps) :: k)
  | StPat pat :: k => guard (cur = None);; close_conj_list k (Some pat) ps
  | StIntuitionistic :: k => p ← cur; close_conj_list k (Some (IIntuitionistic p)) ps
  | StSpatial :: k => p ← cur; close_conj_list k (Some (ISpatial p)) ps
  | StModalElim :: k => p ← cur; close_conj_list k (Some (IModalElim p)) ps
  | StAmp :: k => p ← cur; close_conj_list k None (p :: ps)
  | _ => None
  end.

Fixpoint parse_go (ts : list token) (k : stack) : option stack :=
  match ts with
  | [] => Some k
  | TName "_" :: ts => parse_go ts (StPat IDrop :: k)
  | TName s :: ts => parse_go ts (StPat (IIdent s) :: k)
  | TAnon :: ts => parse_go ts (StPat IFresh :: k)
  | TFrame :: ts => parse_go ts (StPat IFrame :: k)
  | TBracketL :: ts => parse_go ts (StList :: k)
  | TBar :: ts => parse_go ts (StBar :: k)
  | TBracketR :: ts => close_list k [] [] ≫= parse_go ts
  | TParenL :: ts => parse_go ts (StConjList :: k)
  | TAmp :: ts => parse_go ts (StAmp :: k)
  | TParenR :: ts => close_conj_list k None [] ≫= parse_go ts
  | TPure (Some s) :: ts => parse_go ts (StPat (IPure (IGallinaNamed s)) :: k)
  | TPure None :: ts => parse_go ts (StPat (IPure IGallinaAnon) :: k)
  | TIntuitionistic :: ts => parse_go ts (StIntuitionistic :: k)
  | TMinus :: TIntuitionistic :: ts => parse_go ts (StSpatial :: k)
  | TModal :: ts => parse_go ts (StModalElim :: k)
  | TArrow d :: ts => parse_go ts (StPat (IRewrite d) :: k)
  | TPureIntro :: ts => parse_go ts (StPat IPureIntro :: k)
  | (TModalIntro | TIntuitionisticIntro) :: ts => parse_go ts (StPat IModalIntro :: k)
  | TSimpl :: ts => parse_go ts (StPat ISimpl :: k)
  | TDone :: ts => parse_go ts (StPat IDone :: k)
  | TAll :: ts => parse_go ts (StPat IAll :: k)
  | TForall :: ts => parse_go ts (StPat IForall :: k)
  | TBraceL :: ts => parse_clear ts k
  | TNamed :: ts => parse_go ts (StPat INamedPat :: k)
  | _ => None
  end
with parse_clear (ts : list token) (k : stack) : option stack :=
  match ts with
  | TFrame :: TName s :: ts => parse_clear ts (StPat (IClearFrame (SelIdent s)) :: k)
  | TFrame :: TPure None :: ts => parse_clear ts (StPat (IClearFrame SelPure) :: k)
  | TFrame :: TIntuitionistic :: ts => parse_clear ts (StPat (IClearFrame SelIntuitionistic) :: k)
  | TFrame :: TSep :: ts => parse_clear ts (StPat (IClearFrame SelSpatial) :: k)
  | TName s :: ts => parse_clear ts (StPat (IClear (SelIdent s)) :: k)
  | TPure None :: ts => parse_clear ts (StPat (IClear SelPure) :: k)
  | TIntuitionistic :: ts => parse_clear ts (StPat (IClear SelIntuitionistic) :: k)
  | TSep :: ts => parse_clear ts (StPat (IClear SelSpatial) :: k)
  | TBraceR :: ts => parse_go ts k
  | _ => None
  end.

Fixpoint close (k : stack) (ps : list intro_pat) : option (list intro_pat) :=
  match k with
  | [] => Some ps
  | StPat pat :: k => close k (pat :: ps)
  | StIntuitionistic :: k => '(p,ps) ← maybe2 (::) ps; close k (IIntuitionistic p :: ps)
  | StSpatial :: k => '(p,ps) ← maybe2 (::) ps; close k (ISpatial p :: ps)
  | StModalElim :: k => '(p,ps) ← maybe2 (::) ps; close k (IModalElim p :: ps)
  | _ => None
  end.

Definition parse (s : string) : option (list intro_pat) :=
  k ← parse_go (tokenize s) []; close k [].
Ltac parse s :=
  lazymatch type of s with
  | list intro_pat => s
  | list intro_patterns.intro_pat => s
  | intro_pat => constr:([s])
  | intro_patterns.intro_pat => constr:([s])
  | list string =>
     lazymatch eval vm_compute in (mjoin <$> mapM intro_pat.parse s) with
     | Some ?pats => pats
     | _ => fail "intro_pat.parse: cannot parse" s "as an introduction pattern"
     end
  | string =>
     lazymatch eval vm_compute in (intro_pat.parse s) with
     | Some ?pats => pats
     | _ => fail "intro_pat.parse: cannot parse" s "as an introduction pattern"
     end
  | ident => constr:([IIdent s])
  | ?X => fail "intro_pat.parse: the term" s
     "is expected to be an introduction pattern"
     "(usually a string),"
     "but has unexpected type" X
  end.
Ltac parse_one s :=
  lazymatch type of s with
  | intro_pat => s
  | intro_patterns.intro_pat => s
  | string =>
     lazymatch eval vm_compute in (parse s) with
     | Some [?pat] => pat
     | _ => fail "intro_pat.parse_one: cannot parse" s "as an introduction pattern"
     end
  | ?X => fail "intro_pat.parse_one: the term" s
     "is expected to be an introduction pattern"
     "(usually a string),"
     "but has unexpected type" X
  end.
End intro_pat.
(* end intro_patterns.v *)

Module __test.
  Lemma parse_named :
    intro_pat.parse "[@ $]" = Some [IList [[INamedPat; IFrame]]].
  Proof. cbv. reflexivity. Qed.
End __test.

(* copy of proofmode/ltac_tactics.v *)
Ltac _iIntros_go pats startproof :=
  lazymatch type of pats with
  | list intro_patterns.intro_pat =>
      ltac_tactics._iIntros_go pats startproof
  | _ =>
  lazymatch pats with
  | [] =>
    lazymatch startproof with
    | true => iStartProof
    | false => idtac
    end
  (* Optimizations to avoid generating fresh names *)
  | IPure (IGallinaNamed ?s) :: ?pats =>
     let i := fresh in
     _iIntro (i);
     rename_by_string i s;
     _iIntros_go pats startproof
  | IPure IGallinaAnon :: ?pats => _iIntro (?); _iIntros_go pats startproof
  | IIntuitionistic (IIdent ?H) :: ?pats => _iIntroPersistent H; _iIntros_go pats false
  | IDrop :: ?pats => _iIntroDrop; _iIntros_go pats startproof
  | IIdent ?H :: ?pats => _iIntroSpatial H; _iIntros_go pats startproof
  (* Introduction patterns that can only occur at the top-level *)
  | IPureIntro :: ?pats => iPureIntro; _iIntros_go pats false
  | IModalIntro :: ?pats => iModIntro; _iIntros_go pats false
  | IForall :: ?pats => repeat _iIntroForall; _iIntros_go pats startproof
  | IAll :: ?pats => repeat (_iIntroForall || _iIntro); _iIntros_go pats startproof
  (* Clearing and simplifying introduction patterns *)
  | ISimpl :: ?pats => simpl; _iIntros_go pats startproof
  | IClear ?H :: ?pats => iClear H; _iIntros_go pats false
  | IClearFrame ?H :: ?pats => iFrame H; _iIntros_go pats false
  | IDone :: ?pats => try done; _iIntros_go pats startproof
  (* Introduction + destruct *)
  | IIntuitionistic ?pat :: ?pats =>
     let H := iFresh in _iIntroPersistent H; iDestructHyp H as pat; _iIntros_go pats false
  | ?pat :: ?pats =>
     let H := iFresh in _iIntroSpatial H; iDestructHyp H as pat; _iIntros_go pats false
  end
  end.

Ltac _iIntros0 pat ::=
  let pats := intro_pat.parse pat in
  lazymatch pats with
  | [] => idtac
  | _ => _iIntros_go pats true
  end.



(** [pat0] is the unparsed pattern, and is only used in error messages *)
Ltac _iDestructHypGo Hz pat0 pat :=
  lazymatch type of pat with
  | intro_patterns.intro_pat =>
      ltac_tactics._iDestructHypGo Hz pat0 pat
  | _ =>
  lazymatch pat with
  | IFresh =>
     lazymatch Hz with
     | IAnon _ => idtac
     | INamed ?Hz => let Hz' := iFresh in iRename Hz into Hz'
     end
  | IDrop => _iClearHyp Hz
  | IFrame => iFrame Hz
  | IIdent Hz => idtac
  | IIdent ?y => iRename Hz into y
  | INamedPat => iNamed Hz
  | IList [[]] => iExFalso; iExact Hz

  (* conjunctive patterns like [H1 H2] *)
  | IList [[?pat1; IDrop]] =>
     let x := _ident_for_pat_default pat1 Hz in
     _iAndDestructChoice Hz Left x;
     _iDestructHypGo x pat0 pat1
  | IList [[IDrop; ?pat2]] =>
     let x := _ident_for_pat_default pat2 Hz in
     _iAndDestructChoice Hz Right x;
     _iDestructHypGo x pat0 pat2
  (* [% ...] is always interpreted as an existential; there are [IntoExist]
  instances in place to handle conjunctions with a pure left-hand side this way
  as well. *)
  | IList [[IPure IGallinaAnon; ?pat2]] =>
     let x := _ident_for_pat_default pat2 Hz in
     _iExistDestruct Hz as ? x; _iDestructHypGo x pat0 pat2
  | IList [[IPure (IGallinaNamed ?s); ?pat2]] =>
     let x := fresh in
     let y := _ident_for_pat_default pat2 Hz in
     _iExistDestruct Hz as x y;
     rename_by_string x s;
     _iDestructHypGo y pat0 pat2
  | IList [[?pat1; ?pat2]] =>
     (* We have to take care of not using the same name for the two hypotheses:
        [_ident_for_pat_default] will thus only reuse [Hz] (which could in principle
        clash with a name from [pat2]) if it is an anonymous name. *)
     let x1 := _ident_for_pat_default pat1 Hz in
     let x2 := _ident_for_pat pat2 in
     _iAndDestruct Hz x1 x2;
     _iDestructHypGo x1 pat0 pat1; _iDestructHypGo x2 pat0 pat2
  | IList [_ :: _ :: _] => fail "iDestruct:" pat0 "has too many conjuncts"
  | IList [[_]] => fail "iDestruct:" pat0 "has just a single conjunct"

  (* disjunctive patterns like [H1|H2] *)
  | IList [[?pat1];[?pat2]] =>
     let x1 := _ident_for_pat_default pat1 Hz in
     let x2 := _ident_for_pat_default pat2 Hz in
     iOrDestruct Hz as x1 x2;
     [_iDestructHypGo x1 pat0 pat1|_iDestructHypGo x2 pat0 pat2]
  (* this matches a list of three or more disjunctions [H1|H2|H3] *)
  | IList (_ :: _ :: _ :: _) => fail "iDestruct:" pat0 "has too many disjuncts"
  (* the above patterns don't match [H1 H2|H3] *)
  | IList [_;_] => fail "iDestruct: in" pat0 "a disjunct has multiple patterns"

  | IPure IGallinaAnon => iPure Hz as ?
  | IPure (IGallinaNamed ?s) =>
     let x := fresh in
     iPure Hz as x;
     rename_by_string x s
  | IRewrite Right => iPure Hz as ->
  | IRewrite Left => iPure Hz as <-
  | IIntuitionistic ?pat =>
    let x := _ident_for_pat_default pat Hz in
    _iIntuitionistic Hz x; _iDestructHypGo x pat0 pat
  | ISpatial ?pat =>
    let x := _ident_for_pat_default pat Hz in
    _iSpatial Hz x; _iDestructHypGo x pat0 pat
  | IModalElim ?pat =>
    let x := _ident_for_pat_default pat Hz in
    iModCore Hz as x; _iDestructHypGo x pat0 pat
  | _ => fail "iDestruct (named):" pat0 "is not supported due to" pat
  end
  end.
Ltac _iDestructHypFindPat Hgo pat found pats :=
  lazymatch pats with
  | [] =>
    lazymatch found with
    | true => pm_prettify (* post-tactic prettification *)
    | false => fail "iDestruct:" pat "should contain exactly one proper introduction pattern"
    end
  | ISimpl :: ?pats => simpl; _iDestructHypFindPat Hgo pat found pats
  | IClear ?H :: ?pats => iClear H; _iDestructHypFindPat Hgo pat found pats
  | IClearFrame ?H :: ?pats => iFrame H; _iDestructHypFindPat Hgo pat found pats
  | ?pat1 :: ?pats =>
     lazymatch found with
     | false => _iDestructHypGo Hgo pat pat1; _iDestructHypFindPat Hgo pat true pats
     | true => fail "iDestruct:" pat "should contain exactly one proper introduction pattern"
     end
  end.

Ltac _iDestructHyp0 H pat ::=
  let pats := intro_pat.parse pat in
  _iDestructHypFindPat H pat false pats.
