signature VAR = sig
  type t
  val eq : t -> t -> bool
  val named : string -> t
  val freshen : t -> t
  val name : t -> string
  val toString : t -> string
end

structure Var :> VAR =
struct
  type t = string * int
  fun eq (x : t) (y : t) : bool = x = y

  val next = ref 0

  fun get_next () = (next := !next + 1; !next)

  fun named s = (s, get_next())

  fun freshen (s, _) = named s

  fun name (s, _) = s

  fun toString (s, n) = s (* ^ "@" ^ Int.toString n *)
end

signature EXPR = sig
  datatype 'a binder = Bind of Var.t * 'a

  datatype 'a view = Var of Var.t
                   | Lam of 'a binder
                   | Ap of 'a * 'a
                   | Pi of 'a * 'a binder
                   | Univ of int
                   | Tt
                   | Eq of 'a * 'a * 'a
                   | Isect of 'a * 'a binder

  type expr

  val alphaEq : expr -> expr -> bool

  val outof : expr -> expr view
  val into : expr view -> expr

  val ` : expr view -> expr

  val rename : Var.t -> Var.t -> expr -> expr

  val subst : Var.t -> expr -> expr -> expr

  val toString : expr -> string

  val freeIn : Var.t -> expr -> bool
end

structure Expr :> EXPR = struct
  datatype 'a binder = Bind of Var.t * 'a

  datatype 'a view = Var of Var.t
                   | Lam of 'a binder
                   | Ap of 'a * 'a
                   | Pi of 'a * 'a binder
                   | Univ of int
                   | Tt
                   | Eq of 'a * 'a * 'a
                   | Isect of 'a * 'a binder

  structure Internal = struct
    datatype 'a closed_binder = CBind of Var.t * 'a

    datatype expr =
      Bound of int
    | Free of Var.t

    | Lam of expr closed_binder
    | Ap of expr * expr
    | Pi of expr * expr closed_binder
    | Univ of int
    (*
    | Pair of expr * expr
    | Fst of expr
    | Snd of expr
    | Sig of binding_info * expr * expr
    *)
    | Tt
    (*
    | Inl of expr
    | Inr of expr
    | Sum of expr * expr

    | Zero
    | Succ of expr
    | Natrec of expr * expr * binding_info * expr
    | Nat

    | Nil
    | Cons of expr * expr
    | Listrec of expr * expr * binding_info * binding_info * expr
    | List of expr
    *)

    | Eq of expr * expr * expr
    | Isect of expr * expr closed_binder
(*
    | Ceq of expr * expr
*)

    fun opn to e =
      let fun go from (Bound b) = if from = b then to else Bound b
            | go from (Free f) = Free f
            | go from (Lam (CBind (x, e))) = Lam (CBind (x, go (from + 1) e))
            | go from (Ap (e1, e2)) = Ap (go from e1, go from e2)
            | go from (Pi (e1, CBind (x, e2))) = Pi (go from e1, CBind (x, go (from + 1) e2))
            | go from (Univ i) = Univ i
            | go from Tt = Tt
            | go from (Eq (e1, e2, e3)) = Eq (go from e1, go from e2, go from e3)
            | go from (Isect (e1, CBind (x, e2))) =
              Isect (go from e1, CBind (x, go (from + 1) e2))
      in
          go 0 e
      end


    fun close from e =
      let fun go to (Bound b) = Bound b
            | go to (Free f) = if Var.eq from f then Bound to else Free f
            | go to (Lam (CBind (x, e))) = Lam (CBind (x, go (to + 1) e))
            | go to (Ap (e1, e2)) = Ap (go to e1, go to e2)
            | go to (Pi (e1, CBind (x, e2))) = Pi (go to e1, CBind (x, go (to + 1) e2))
            | go to (Univ i) = Univ i
            | go to Tt = Tt
            | go to (Eq (e1, e2, e3)) = Eq (go to e1, go to e2, go to e3)
            | go to (Isect (e1, CBind (x, e2))) = Isect (go to e1, CBind (x, go (to + 1) e2))
      in
          go 0 e
      end

    fun subst from to e = opn to (close from e)

    fun rename from to e = opn (Free to) (close from e)

    fun bind (Bind (from, e)) = CBind (from, (close from e))

    fun unbind (CBind (to, e)) =
      let val to = Var.freshen to
      in
          Bind (to, opn (Free to) e)
      end


    (** Not quite structural equality (=), since we want to ignore the name
        annotations at binding sites. *)
    fun alphaEq (Bound b1) (Bound b2) = b1 = b2
      | alphaEq (Free f1) (Free f2) = Var.eq f1 f2
      | alphaEq (Lam (CBind (_, e1))) (Lam (CBind (_, e2))) = alphaEq e1 e2
      | alphaEq (Ap (e11, e12)) (Ap (e21, e22)) = alphaEq e11 e21 andalso alphaEq e12 e22
      | alphaEq (Pi (e11, CBind (_, e12))) (Pi (e21, CBind (_, e22))) =
        alphaEq e11 e21 andalso alphaEq e12 e22
      | alphaEq (Univ i1) (Univ i2) = i1 = i2
      | alphaEq (Eq (e11, e12, e13)) (Eq (e21, e22, e23)) =
        alphaEq e11 e21 andalso alphaEq e12 e22 andalso alphaEq e13 e23
      | alphaEq Tt Tt = true
      | alphaEq (Isect (e11, CBind (_, e12))) (Isect (e21, CBind (_, e22))) =
        alphaEq e11 e21 andalso alphaEq e12 e22
      | alphaEq _ _ = false

    fun freeIn v e =
      let fun go (Bound b) = false
            | go (Free f) = Var.eq v f
            | go (Lam (CBind (x, e))) = go e
            | go (Ap (e1, e2)) = go e1 orelse go e2
            | go (Pi (e1, CBind (x, e2))) = go e1 orelse go e2
            | go (Univ i) = false
            | go Tt = false
            | go (Eq (e1, e2, e3)) = go e1 orelse go e2 orelse go e3
            | go (Isect (e1, CBind (x, e2))) = go e1 orelse go e2
      in
          go e
      end

    val TOP = 4
    val LAM = 3
    val AP = 2
    val BOT = 0

    datatype side = LEFT | RIGHT | NO

    (** (1) This is kind of messy because we're actually doing pretty printing here,
            so we need to keep track of precedence and associativity of various operators.
        (2) It's better to do this "internally" (directly on the LN representation)
            rather than "externally" (via the view mechanism) because then we can see
            exactly what unique ids are on each free variable and binding annotation.
            The view mechanism does a bunch of freshening and opening that obscures the
            original ids. For anything but debugging the binding structure, the other way
            would be fine. But for debugging binding this is much better.
     *)
    fun toString e =
      let fun prec_of (Free _) = BOT
            | prec_of (Bound _) = BOT
            | prec_of (Lam _) = LAM
            | prec_of (Ap _) = AP
            | prec_of (Pi _) = LAM
            | prec_of (Univ _) = BOT
            | prec_of Tt = BOT
            | prec_of (Eq _) = LAM
            | prec_of (Isect _) = LAM

          fun assoc_of (Free _) = NO
            | assoc_of (Bound _) = NO
            | assoc_of (Lam _) = RIGHT
            | assoc_of (Ap _) = LEFT
            | assoc_of (Pi _) = RIGHT
            | assoc_of (Univ _) = NO
            | assoc_of Tt = NO
            | assoc_of (Eq _) = RIGHT
            | assoc_of (Isect _) = RIGHT


          fun no_parens prec side e =
            prec > prec_of e orelse
            (prec = prec_of e andalso assoc_of e = side andalso side <> NO)

          fun one env e =
            case e of
                Free v => Var.toString v
              | Bound b => Var.toString (List.nth (env, b))
              | Lam (CBind (v, e)) =>
                "\\" ^ Var.toString v ^ ". " ^ go (v :: env) LAM RIGHT e
              | Ap (e1, e2) => go env AP LEFT e1 ^ " " ^ go env AP RIGHT e2
              | Pi (e1, CBind (v, e2)) =>
                if freeIn v e2
                then
                    "(" ^ Var.toString v ^ " : " ^
                    go env TOP NO e1 ^ ") -> " ^
                    go (v :: env) LAM RIGHT e2
                else go env LAM LEFT e1 ^ " -> " ^
                     go (v :: env) LAM RIGHT e2
              | Univ i => "U{" ^ Int.toString i ^ "}"
              | Tt => "tt"
              | Eq (e1, e2, e3) =>
                if alphaEq e1 e2
                then go env LAM NO e1 ^ " in " ^
                     go env LAM RIGHT e3
                else go env LAM NO e1 ^ " = " ^
                     go env LAM NO e2 ^ " in " ^
                     go env LAM RIGHT e3
              | Isect (e1, CBind (v, e2)) => "{" ^ Var.toString v ^ " : " ^
                                             go env TOP NO e1 ^ "} " ^
                                             go (v :: env) LAM RIGHT e2

          and go (env : Var.t list) (prec : int) (side : side) (e : expr) : string =
              let val s = one env e
              in if no_parens prec side e
                 then s
                 else "(" ^ s ^ ")"
              end
      in go [] TOP NO e end

  end
  structure I = Internal
  type 'a closed_binder = 'a I.closed_binder

  type expr = I.expr
  val bind = I.bind
  val unbind = I.unbind

  val alphaEq = I.alphaEq

  val rename = I.rename
  val subst = I.subst
  val freeIn = I.freeIn

  exception NotLocallyClosed

  fun outof (I.Bound _) = raise NotLocallyClosed
    | outof (I.Free v) = Var v
    | outof (I.Lam xe) = Lam (unbind xe)
    | outof (I.Ap (e1, e2)) = Ap (e1, e2)
    | outof (I.Pi (e1, xe2)) = Pi (e1, unbind xe2)
    | outof (I.Univ i) = Univ i
    | outof I.Tt = Tt
    | outof (I.Eq (e1, e2, e3)) = Eq (e1, e2, e3)
    | outof (I.Isect (e1, xe2)) = Isect (e1, unbind xe2)

  fun into (Var v) = I.Free v
    | into (Lam xe) = I.Lam (bind xe)
    | into (Ap (e1, e2)) = I.Ap (e1, e2)
    | into (Pi (e1, xe2)) = I.Pi (e1, bind xe2)
    | into (Univ i) = I.Univ i
    | into Tt = I.Tt
    | into (Eq (e1, e2, e3)) = I.Eq (e1, e2, e3)
    | into (Isect (e1, xe2)) = I.Isect (e1, bind xe2)

  fun ` v = into v

  val toString = I.toString
end

structure Conv = struct
  open Expr

  fun deep f e =
    let val e' =
        case outof e of
            Var v => ` (Var v)
          | Lam (Bind (x, e)) => ` (Lam (Bind (x, deep f e)))
          | Ap (e1, e2) => ` (Ap (deep f e1, deep f e2))
          | Pi (e1, Bind (x, e2)) => ` (Pi (deep f e1, Bind (x, deep f e2)))
          | Univ i => ` (Univ i)
          | Tt => ` Tt
          | Eq (e1, e2, e3) => ` (Eq (deep f e1, deep f e2, deep f e3))
          | Isect (e1, Bind (x, e2)) => ` (Isect (deep f e1, Bind (x, deep f e2)))
    in
        f e'
    end
end

structure Eval = struct
  datatype result = Stuck | Value | Step of Expr.expr

  fun step (e : Expr.expr) : result =
    case Expr.outof e of
       Expr.Var _ => Value
     | Expr.Lam _ => Value
     | Expr.Ap (e1, e2) =>
      (case step e1 of
           Stuck => Stuck
         | Value => (case Expr.outof e1 of
                         Expr.Lam (Expr.Bind (x, e)) => Step (Expr.subst x e2 e)
                       | _ => Stuck)
         | Step e1' => Step (Expr.into (Expr.Ap (e1', e2))))
    | Expr.Pi _ => Value
    | Expr.Univ _ => Value
    | Expr.Tt => Value
    | Expr.Eq _ => Value
    | Expr.Isect _ => Value

  fun eval e =
    case step e of
        Step e => eval e
      | _ => e
end

structure ListUtil = struct
  fun assoc (k : string) [] = raise Subscript
    | assoc k ((k1,v1) :: l) = if k = k1 then v1 else assoc k l
end

structure ExprAst = struct
  datatype t =
    Var of string

  | Lam of string * t
  | Ap of t * t
  | Pi of string * t * t
  | Univ of int
  | Tt
  | Eq of t * t * t
  | Isect of string * t * t

  fun toExpr env a =
    let fun go env (Var s) =
          let in
              Expr.into (Expr.Var (ListUtil.assoc s env))
              handle Subscript => raise Fail ("Unbound variable " ^ s)
          end

          | go env (Lam (x, e)) =
            let val v = Var.named x
            in Expr.into (Expr.Lam (Expr.Bind (v, go ((x, v) :: env) e))) end
          | go env (Ap (e1, e2)) = Expr.into (Expr.Ap (go env e1, go env e2))
          | go env (Pi (x, e1, e2)) =
            let val v = Var.named x
            in Expr.into (Expr.Pi (go env e1, Expr.Bind (v, go ((x, v) :: env) e2))) end
          | go env (Univ i) = Expr.into (Expr.Univ i)
          | go env Tt = Expr.into Expr.Tt
          | go env (Eq (e1, e2, e3)) =
            Expr.into (Expr.Eq (go env e1, go env e2, go env e3))
          | go env (Isect (x, e1, e2)) =
            let val v = Var.named x
            in Expr.into (Expr.Isect (go env e1, Expr.Bind (v, go ((x, v) :: env) e2))) end
    in go env a end

  local
      fun bad_toExpr a =
        let fun go env (Var s) =
                let in
                    Expr.into (Expr.Var (ListUtil.assoc s env))
                    handle Subscript => Expr.into (Expr.Var (Var.named s))
                end
              | go env (Lam (x, e)) =
                let val v = Var.named x
                in Expr.into (Expr.Lam (Expr.Bind (v, go ((x, v) :: env) e))) end
              | go env (Ap (e1, e2)) = Expr.into (Expr.Ap (go env e1, go env e2))
              | go env (Pi (x, e1, e2)) =
                let val v = Var.named x
                in Expr.into (Expr.Pi (go env e1, Expr.Bind (v, go ((x, v) :: env) e2))) end
              | go env (Univ i) = Expr.into (Expr.Univ i)
              | go env Tt = Expr.into Expr.Tt
              | go env (Eq (e1, e2, e3)) =
                Expr.into (Expr.Eq (go env e1, go env e2, go env e3))
              | go env (Isect (x, e1, e2)) =
                let val v = Var.named x
                in Expr.into (Expr.Isect (go env e1, Expr.Bind (v, go ((x, v) :: env) e2))) end

        in go [] a end
  in
    fun toString a =
      let val e = bad_toExpr a
      in Expr.toString e end
  end
end

structure TacticAst = struct
  datatype t =
    Id
  | Intro of ExprAst.t option * string option
  | Elim of string * ExprAst.t option
  | Eq of ExprAst.t option
  | Fail
  | Then of t * t
  | ThenL of t * t list
  | OrElse of t * t
  | Hyp of string
  | HypEq
  | Reduce

  fun withToString NONE = ""
    | withToString (SOME e) = " with " ^ ExprAst.toString e

  fun asToString NONE = ""
    | asToString (SOME x) = " as " ^ x

  fun toString Id = "id"
    | toString (Eq oe) = "eq" ^ withToString oe
    | toString Fail = "fail"
    | toString (Intro (oe, ox)) = "intro" ^ withToString oe ^ asToString ox
    | toString (Elim (x, oe)) = "elim " ^ x ^ withToString oe
    | toString (Then (t1, t2)) = toString t1 ^ "; " ^ toString t2
    | toString (ThenL (t, l)) =
      let fun go [] = ""
            | go [t] = toString t
            | go (t :: ts) = toString t ^ ", " ^ go ts
      in toString t ^ "; [" ^ go l ^ "]" end
    | toString (OrElse (t1, t2)) = toString t1 ^ " | " ^ toString t2
    | toString (Hyp x) = "hyp " ^ x
    | toString HypEq = "hypeq"
    | toString Reduce = "reduce"
end

structure CommandAst = struct
  datatype t =
    Definition of string * ExprAst.t
  | Theorem of string * ExprAst.t * TacticAst.t

  fun toString (Definition (name, e)) =
      "definition " ^ name ^ " := " ^ ExprAst.toString e ^ "."
    | toString (Theorem (name, ty, tac)) =
      "theorem " ^ name ^ " : " ^ ExprAst.toString ty ^ " {\n" ^ TacticAst.toString tac ^ "\n}."
end

structure Position = struct
  type t = {line : int, col : int}

  val init : t = {line = 1, col = 0}

  fun next_line {line, col} = {line = line + 1, col = 0}
  fun next_col {line, col} = {line = line, col = col + 1}

  fun toString {line, col} = Int.toString line ^ ":" ^ Int.toString col
end

structure Token = struct
  datatype token =
    Dot | Backslash | LParen | RParen | Arrow | Colon | Id of string
    | Univ of int | Equal
    | LBrace | RBrace | LBracket | RBracket | Comma
    | ColonEqual | SemiColon | VertBar
    | In | As | With

  fun toString Dot = "."
    | toString Backslash = "\\"
    | toString LParen = "("
    | toString RParen = ")"
    | toString Arrow = "->"
    | toString Colon = ":"
    | toString (Id x) = x
    | toString (Univ i) = "U{" ^ Int.toString i ^ "}"
    | toString Equal = "="
    | toString LBrace = "{"
    | toString RBrace = "}"
    | toString LBracket = "["
    | toString RBracket = "]"
    | toString Comma = ","
    | toString ColonEqual = ":="
    | toString SemiColon = ";"
    | toString VertBar = "|"
    | toString With = "With"
    | toString In = "in"
    | toString As = "as"

end

signature TOKENIZER = sig
  exception LexicalError of string

  type token_stream = (Position.t * Token.token) list

  val tokenize : string -> token_stream
end

structure Tokenizer :> TOKENIZER = struct
  exception LexicalError of string

  type token_stream = (Position.t * Token.token) list

  open Position Token

  fun tokenize_word pred p cs =
    let fun go p acc [] = (p, acc, [])
          | go p acc (c :: cs) =
            if pred c
            then go (next_col p) (c :: acc) cs
            else (p, acc, c :: cs)
        val (p, acc, cs) = go p [] cs
        val word = String.implode (List.rev acc)
    in (p, word, cs)
    end

  val tokenize_id : Position.t -> char list -> Position.t * string * char list =
      tokenize_word Char.isAlpha
  val tokenize_int : Position.t -> char list -> Position.t * string * char list =
      tokenize_word Char.isDigit

  fun expect p c (c' :: cs) =
    if c = c' then (next_col p, cs)
    else raise LexicalError (Position.toString p ^ ": Expected character '" ^
                             Char.toString c ^ "' but got '" ^ Char.toString c' ^ "'")
    | expect p c [] =
      raise LexicalError ("Unexpected EOF while looking for character " ^ Char.toString c)


  fun tokenize s =
    let fun go p acc [] = List.rev acc
          | go p acc (#" " :: cs) = go (next_col p) acc cs
          | go p acc (#"\n" :: cs) = go (next_line p) acc cs
          | go p acc (#"." :: cs) = go (next_col p) ((p, Dot) :: acc) cs
          | go p acc (#"\\" :: cs) = go (next_col p) ((p, Backslash) :: acc) cs
          | go p acc (#"(" :: cs) = go (next_col p) ((p, LParen) :: acc) cs
          | go p acc (#")" :: cs) = go (next_col p) ((p, RParen) :: acc) cs
          | go p acc (#"-" :: #">" :: cs) = go (next_col (next_col p)) ((p, Arrow) :: acc) cs

          | go p acc (#":" :: #"=" :: cs) = go (next_col (next_col p)) ((p, ColonEqual) :: acc) cs
          | go p acc (#":" :: cs) = go (next_col p) ((p, Colon) :: acc) cs

          | go p acc (#"U" :: #"{" :: cs) =
            let val (p', i, cs) = tokenize_int (next_col (next_col p)) cs
                val (p', cs) = expect p' #"}" cs
                val SOME i = Int.fromString i
            in go p' ((p, Univ i) :: acc) cs end
          | go p acc (#"=" :: cs) = go (next_col p) ((p, Equal) :: acc) cs

          | go p acc (#"{" :: cs) = go (next_col p) ((p, LBrace) :: acc) cs
          | go p acc (#"}" :: cs) = go (next_col p) ((p, RBrace) :: acc) cs
          | go p acc (#"[" :: cs) = go (next_col p) ((p, LBracket) :: acc) cs
          | go p acc (#"]" :: cs) = go (next_col p) ((p, RBracket) :: acc) cs
          | go p acc (#"," :: cs) = go (next_col p) ((p, Comma) :: acc) cs
          | go p acc (#";" :: cs) = go (next_col p) ((p, SemiColon) :: acc) cs
          | go p acc (#"|" :: cs) = go (next_col p) ((p, VertBar) :: acc) cs

          | go p acc (c :: cs) =
            if Char.isAlpha c
            then let val (p', id, cs) = tokenize_id p (c :: cs)
                 in case id of
                        "in" => go p' ((p, In) :: acc) cs
                      | "as" => go p' ((p, As) :: acc) cs
                      | "with" => go p' ((p, With) :: acc) cs
                      | _ => go p' ((p, Id id) :: acc) cs
                 end
            else raise LexicalError (Position.toString p ^ ": Unexpected character '" ^
                                     Char.toString c ^ "'")
    in go init [] (String.explode s) end
end

(*
  e ::= x | \x. e | (x : e) -> e | e e | U{i} | e = e in e

  tactic ::= id | intro ('with' expr)?  | elim x | eq | fail | hyp x
           | tactic; tactic
           | tactic; '[' sep1(tactic, ',') ']'
           | tactic '|' tactic
           | '(' tactic ')'

  command ::= definition name := expr.
            | theorem name : expr { tactic }.

  ----

  tactic ::= tactic2 (';' '[' sep1(tactic, ',') ']' | ';' tactic2 | '|' tactic)*
  tactic2 ::= fail | id | eq | hyp x
            | intro ('with' expr)? | elim x ('with' expr)?
            | '(' tactic ')'

  expr ::= \x. expr | (x : expr) -> expr | factor
  factor ::= term ('=' term 'in' term)?
  term ::= (x | U{i} | '(' e ')' )*
*)

signature PARSER = sig
  exception ParseError of string
  type 'a parser = Tokenizer.token_stream -> 'a * Tokenizer.token_stream
  val parse_expr : ExprAst.t parser
  val parse_tactic : TacticAst.t parser
  val parse_command : CommandAst.t parser
end

structure Parser :> PARSER = struct
  open Tokenizer Token

  exception ParseError of string

  type 'a parser = Tokenizer.token_stream -> 'a * Tokenizer.token_stream

  fun report_error msg [] =
      raise ParseError ("Unexpected EOF while looking for " ^ msg ^ ".")
    | report_error msg ((p, t) :: ts) =
      raise ParseError (Position.toString p ^ ": Looking for " ^ msg ^
                           " but got " ^ Token.toString t)

  fun detect_id ((p, Id s) :: ts) = (SOME s, ts)
    | detect_id ts = (NONE, ts)

  fun detect_tok (tok : token) ((p, t) :: ts) =
    if tok = t then (SOME (), ts)
    else (NONE, (p, t) :: ts)
    | detect_tok _ ts = (NONE, ts)

  fun expect msg p ts =
    let val (ox, ts) = p ts
    in case ox of
           SOME x => (x, ts)
         | NONE => report_error msg ts
    end

  fun expect_id msg ts = expect msg detect_id ts

  fun expect_tok msg tok ts = expect ("token " ^ Token.toString tok ^ " as part of " ^ msg)
                                     (detect_tok tok) ts

  fun parse_expr ((_, Backslash) :: ts) =
    let val (x, ts) = expect_id "name after lambda" ts
        val ((), ts) = expect_tok "lambda" Dot ts
        val (body, ts) = parse_expr ts
    in (ExprAst.Lam (x, body), ts) end
    | parse_expr ((_, LParen) :: (_, Id x) :: (_, Colon) :: ts) =
      let val (lhs, ts) = parse_expr ts
          val ((), ts) = expect_tok "pi" RParen ts
          val ((), ts) = expect_tok "pi" Arrow ts
          val (rhs, ts) = parse_expr ts
      in (ExprAst.Pi (x, lhs, rhs), ts) end
    | parse_expr ((_, LBrace) :: (_, Id x) :: (_, Colon) :: ts) =
      let val (lhs, ts) = parse_expr ts
          val ((), ts) = expect_tok "isect" RBrace ts
          val (rhs, ts) = parse_expr ts
      in (ExprAst.Isect (x, lhs, rhs), ts) end
    | parse_expr ts =
      let val (f, ts) = parse_factor ts
          val (ou, ts) = detect_tok Arrow ts
      in case ou of
             NONE => (f, ts)
           | SOME () =>
             let val (e, ts) = parse_expr ts
             in (ExprAst.Pi ("_", f, e), ts) end
      end

  and parse_factor ts =
      let val (e1, ts) = parse_term ts
      in case ts of
             (_, Equal) :: ts =>
             let val (e2, ts) = parse_term ts
                 val ((), ts) = expect_tok "equality" In ts
                 val (e3, ts) = parse_expr ts
             in (ExprAst.Eq (e1, e2, e3), ts) end
           | (_, In) :: ts =>
             let val (e3, ts) = parse_expr ts
             in (ExprAst.Eq (e1, e1, e3), ts) end
           | _ => (e1, ts)
      end
  and parse_term ts =
      let fun parse_one_term ((_, Id "tt") :: ts) = (SOME ExprAst.Tt, ts)
            | parse_one_term ((_, Id x) :: ts) = (SOME (ExprAst.Var x), ts)
            | parse_one_term ((_, LParen) :: ts) =
              let val (e, ts) = parse_expr ts
                  val ((), ts) = expect_tok "parenthesized term" RParen ts
              in (SOME e, ts) end
            | parse_one_term ((_, Univ i) :: ts) = (SOME (ExprAst.Univ i), ts)
            | parse_one_term ts = (NONE, ts)
          fun go acc ts =
            case parse_one_term ts of
                (NONE, ts) => (acc, ts)
              | (SOME f, ts) => go (ExprAst.Ap (acc, f)) ts
          val (tm, ts) = parse_one_term ts
      in case tm of
             NONE => report_error "term" ts
           | SOME f => go f ts
      end

  fun parse_with ((_, With) :: ts) =
      let val (e, ts) = parse_expr ts
      in (SOME e, ts) end
    | parse_with ts = (NONE, ts)

  fun parse_as ((_, As) :: ts) =
      let val (x, ts) = expect_id "name after 'as'" ts
      in (SOME x, ts) end
    | parse_as ts = (NONE, ts)


  fun parse_sep1 parse_item parse_sep ts =
    let fun go acc ts =
          let val (sep, ts) = parse_sep ts
          in case sep of
                 NONE => (List.rev acc, ts)
               | SOME _ =>
                 let val (item, ts) = parse_item ts
                 in go (item :: acc) ts end
          end
        val (x, ts) = parse_item ts
    in go [x] ts end

  fun parse_tactic ts =
    let fun go acc ((_, SemiColon) :: (_, LBracket) :: ts) =
            let val (l, ts) = parse_sep1 parse_tactic (detect_tok Comma) ts
                val ((), ts) = expect_tok "tactic list" RBracket ts
            in go (TacticAst.ThenL (acc, l)) ts end
          | go acc ((_, SemiColon) :: ts) =
            let val (tac, ts) = parse_tactic2 ts
            in go (TacticAst.Then (acc, tac)) ts end
          | go acc ((_, VertBar) :: ts) =
            let val (tac, ts) = parse_tactic ts
            in (TacticAst.OrElse (acc, tac), ts) end
          | go acc ts = (acc, ts)
        val (tac, ts) = parse_tactic2 ts
    in go tac ts end
  and parse_tactic2 ((_, Id "fail") :: ts) = (TacticAst.Fail, ts)
    | parse_tactic2 ((_, Id "id") :: ts) = (TacticAst.Id, ts)
    | parse_tactic2 ((_, Id "eq") :: ts) =
      let val (oe, ts) = parse_with ts
      in (TacticAst.Eq oe, ts) end
    | parse_tactic2 ((_, Id "intro") :: ts) =
      let val (oe, ts) = parse_with ts
          val (ox, ts) = parse_as ts
      in (TacticAst.Intro (oe, ox), ts) end
    | parse_tactic2 ((_, Id "elim") :: ts) =
      let val (x, ts) = expect_id "hypothesis name to eliminate" ts
          val (oe, ts) = parse_with ts
      in (TacticAst.Elim (x, oe), ts) end
    | parse_tactic2 ((_, Id "hyp") :: ts) =
      let val (x, ts) = expect_id "hypothesis name" ts
      in (TacticAst.Hyp x, ts) end
    | parse_tactic2 ((_, Id "hypeq") :: ts) = (TacticAst.HypEq, ts)
    | parse_tactic2 ((_, LParen) :: ts) =
      let val (tac, ts) = parse_tactic ts
          val ((), ts) = expect_tok "parenthesized tactic" RParen ts
      in (tac, ts) end
    | parse_tactic2 ((_, Id "reduce") :: ts) = (TacticAst.Reduce, ts)
    | parse_tactic2 ts = report_error "tactic" ts


  fun parse_command ((_, Id "definition") :: ts) =
      let val (name, ts) = expect_id "name of definition" ts
          val ((), ts) = expect_tok "definition" ColonEqual ts
          val (e, ts) = parse_expr ts
          val ((), ts) = expect_tok "definition" Dot ts
      in (CommandAst.Definition (name, e), ts) end
    | parse_command ((_, Id "theorem") :: ts) =
      let val (name, ts) = expect_id "name of theorem" ts
          val ((), ts) = expect_tok "theorem" Colon ts
          val (e, ts) = parse_expr ts
          val ((), ts) = expect_tok "theorem" LBrace ts
          val (tac, ts) = parse_tactic ts
          val ((), ts) = expect_tok "theorem" RBrace ts
          val ((), ts) = expect_tok "theorem" Dot ts
      in (CommandAst.Theorem (name, e, tac), ts) end
    | parse_command ts = report_error "command" ts
end

signature TELESCOPE = sig
  type t
  val toString : t -> string
  val empty : t
  val isEmpty : t -> bool

  (* the bool says whether the variable must be visible *)
  val lookup : bool -> Var.t -> t -> Expr.expr option

  (* the bool says whether the variable is visible *)
  val extend : bool -> Var.t -> Expr.expr -> t -> t
  val toEnv : t -> (string * Var.t) list
  val map : (Expr.expr -> Expr.expr) -> t -> t
end

structure Telescope :> TELESCOPE = struct
  open Expr

  datatype visibility = Visible | Invisible

  (* stored in reverse! *)
  type t = (Var.t * visibility * Expr.expr) list

  val empty : t = []

  fun toString tel =
    let val lines = List.map (fn (v, vis, e) =>
                                 let val s = Var.toString v ^ " : " ^ Expr.toString e
                                 in case vis of
                                        Visible => s
                                      | Invisible => "[" ^ s ^ "]"
                                 end)
                             (List.rev tel)
    in String.concatWith "\n" lines end

  val isEmpty = List.null

  fun allowed _ Visible = true
    | allowed false _ = true
    | allowed true Invisible = false

  fun lookup b v [] = NONE
    | lookup b v ((x, vis, e) :: tel) =
      if Var.eq v x
      then if allowed b vis
           then SOME e
           else NONE
      else lookup b v tel

  fun extend b x e tel = (x, if b then Visible else Invisible, e) :: tel

  val toEnv : t -> (string * Var.t) list = List.map (fn (v, _, _) => (Var.name v, v))

  val map : (expr -> expr) -> t -> t = fn f => List.map (fn (x, vis, e) => (x, vis, f e))
end

signature SEQUENT = sig
  datatype t = >> of Telescope.t * Expr.expr
  val toString : t -> string
  val ofExpr : Expr.expr -> t
end

structure Sequent : SEQUENT = struct
  datatype t = >> of Telescope.t * Expr.expr

  infix >>

  fun toString (hyps >> conc) : string =
    let val ctx = Telescope.toString hyps
    in ctx ^ (if Telescope.isEmpty hyps then "" else "\n") ^ "|- " ^ Expr.toString conc end

  fun ofExpr e = (Telescope.empty >> e)
end

structure Derivation = struct
  open Expr

  datatype t = Hyp of Var.t
             | HypEq of Var.t
             | PiIntro of Var.t * t * t
             | PiEq of Var.t * t * t
             | UniEq of int
             | LamEq of Var.t * t * t
             | IsectIntro of Var.t * t * t
             | IsectEq of Var.t * t * t

  fun extract (Hyp x) = `(Var x)
    | extract (HypEq x) = `Tt
    | extract (PiIntro (x, A, B)) = `(Lam (Bind (x, extract B)))
    | extract (PiEq (x, A, B)) = `Tt
    | extract (UniEq _) = `Tt
    | extract (LamEq (x, e1, e2)) = `Tt
    | extract (IsectIntro (x, A, B)) = subst x (`Tt) (extract B)
    | extract (IsectEq (x, A, B)) = `Tt
end

structure TacticResult = struct
  type t = {subgoals : Sequent.t list,
            evidence : Derivation.t list -> Derivation.t}
end

structure Tactic = struct
  type t = Sequent.t -> TacticResult.t

  exception InternalError of string
  exception ExternalError of string

  fun ID s = {subgoals = [s],
              evidence = (fn [d] => d | _ => raise InternalError "Tactic.ID")}

  fun FAIL msg s = raise ExternalError ("FAIL: " ^ msg)

  local
      fun zipWith f [] [] = []
        | zipWith f (x :: xs) (y :: ys) = f x y :: zipWith f xs ys
        | zipWith _ _ _ = raise InternalError "zipWith"

      fun split [] [] = []
        | split (x :: xs) ys =
          let val first = List.take (ys, List.length x)
              val rest = List.drop (ys, List.length x)
          in
              first :: split xs rest
          end
        | split _ _ = raise InternalError "split"
  in
  fun THEN (t1, t2) = fn s =>
    let val {subgoals = s1, evidence = ev1} = t1 s
        val rs = List.map t2 s1
        val ss = List.map (fn {subgoals = s, evidence = _} => s) rs
        val evs = List.map (fn {subgoals = _, evidence = e} => e) rs
    in
        {subgoals = List.concat ss,
         evidence = fn l => ev1 (zipWith (fn f => fn x => f x) evs (split ss l))}
    end

  fun THENL (t1, l) = fn s =>
    let val {subgoals = s1, evidence = ev1} = t1 s
        val rs = zipWith (fn f => fn x => f x) l s1
        val ss = List.map (fn {subgoals = s, evidence = _} => s) rs
        val evs = List.map (fn {subgoals = _, evidence = e} => e) rs
    in
        {subgoals = List.concat ss,
         evidence = fn l => ev1 (zipWith (fn f => fn x => f x) evs (split ss l))}
    end
  end

  fun ORELSE (t1, t2) = fn s =>
    t1 s
    handle ExternalError _ => t2 s
end

structure Rules = struct
  open Sequent Tactic

  infix >>

  fun (x, e) :: tel = Telescope.extend true x e tel

  infix :::
  fun (x, b, e) ::: tel = Telescope.extend b x e tel

  fun getHyp b x H =
    let val x = ListUtil.assoc x (Telescope.toEnv H)
    in case Telescope.lookup b x H of
           NONE => raise Subscript
         | SOME ty => (x, ty)
    end
    handle Subscript => raise ExternalError ("Unknown hypothesis " ^ x)


  structure General = struct
    fun Hyp x (H >> C) =
      let val (x, ty) = getHyp true x H
      in if not (Expr.alphaEq ty C)
         then raise ExternalError ("Hyp: Hypothesis " ^ Var.toString x ^ " has type " ^
                               Expr.toString ty ^ " rather than goal type " ^
                               Expr.toString C)
         else { subgoals = [], evidence = fn _ => Derivation.Hyp x }
      end

    fun HypEq (H >> C) =
      case Expr.outof C of
          Expr.Eq (lhs, rhs, ty') =>
          (case (Expr.outof lhs, Expr.outof rhs) of
               (Expr.Var l, Expr.Var r) =>
               if not (Var.eq l r)
               then raise ExternalError ("Goal consists of different variables " ^
                                         Var.toString l ^ " and " ^ Var.toString r ^ ".")
               else {subgoals = [], evidence = fn _ => Derivation.HypEq l}
             | _ => raise ExternalError ("HypEq expects an equality goal between vars " ^
                                         "but got " ^ Expr.toString lhs ^ " and " ^
                                         Expr.toString rhs))
        | _ => raise ExternalError ("HypEq expects equality goal rather than " ^
                                    Expr.toString C)



    fun Reduce (H >> C) =
      { subgoals = [Telescope.map (Conv.deep Eval.eval) H >> Conv.deep Eval.eval C],
        evidence = fn [d] => d | _ => raise InternalError "Reduce" }
  end

  structure Pi = struct
    open Expr

    (* H >> (x : A) -> B
     *     H >> A in U{i}
     *     H, x : A >> B
     *)
    fun Intro level ox (H >> C) =
      let val (A, x, B) = case outof C of
                              Pi (A, Bind (x, B)) => (A, x, B)
                           | _ => raise ExternalError "Pi.Intro expects conclusion to be Pi"
          val (x, B) = case ox of
                           NONE => (x, B)
                         | SOME y => let val y = Var.named y
                                     in (y, rename x y B) end
      in
          {subgoals = [H >> `(Eq (A, A, `(Univ level))),
                       (x, A) :: H >> B],
           evidence = fn [d1, d2] => Derivation.PiIntro (x, d1, d2)
           | _ => raise InternalError "Pi.Intro" }
      end


    (* H >> (\x. e1) = (\x. e2) in (x : A) -> B
     *     H >> A in U{i}
     *     H, x : A >> e1 = e2 in B
     *)
    fun LamEq level (H >> C) =
      let val (x, e1, y, e2, A, z, B) =
              case outof C of
                  Eq (lhs, rhs, ty) =>
                  (case (outof lhs, outof rhs, outof ty) of
                       (Lam (Bind (x, e1)),  Lam (Bind (y, e2)), Pi (A, Bind (z, B))) =>
                       (x, e1, y, e2, A, z, B)
                    | _ => raise ExternalError "Pi.LamEq expects an equality between lambdas in a Pi type")
               | _ => raise ExternalError "Pi.LamEq expects an equality"
      in { subgoals = [H >> `(Eq (A, A, `(Univ level))),
                       (x, A) :: H >> `(Eq (e1, rename y x e2, rename z x B))],
           evidence = fn [d1, d2] => Derivation.LamEq (x, d1, d2)
                      | _ => raise InternalError "Pi.LamEq"}
      end

    (* H >> (x : A1) -> B1 = (x : A2) -> B2 in U{i}
     *     H >> A1 = A2 in U{i}
     *     H, x : A1 >> B1 = B2 in U{i}
     *)
    fun Eq (H >> C) =
      let val (x, A1, B1, y, A2, B2, i) =
              case outof C of
                  Expr.Eq (lhs, rhs, ty) =>
                  (case (outof lhs, outof rhs, outof ty) of
                       (Pi (A1, Bind (x, B1)), Pi (A2, Bind (y, B2)), Univ i) =>
                       (x, A1, B1, y, A2, B2, i)
                     | _ => raise ExternalError "Pi.Eq expects an equality between pis in a universe")
               | _ => raise ExternalError "Pi.Eq expects an equality"
      in { subgoals = [H >> `(Expr.Eq (A1, A2, `(Univ i))),
                       (x, A1) :: H >> `(Expr.Eq (B1, rename y x B2, `(Univ i)))],
           evidence = fn [d1, d2] => Derivation.PiEq (x, d1, d2)
                              | _ => raise InternalError "Pi.Eq" }
      end
  end

  structure Isect = struct
    open Expr

    (* H >> {x : A} -> B
     *     H >> A in U{i}
     *     H, [x : A] >> B
     *)
    fun Intro level ox (H >> C) =
      let val (A, x, B) = case outof C of
                              Isect (A, Bind (x, B)) => (A, x, B)
                           | _ => raise ExternalError "Isect.Intro expects conclusion to be Isect"
          val (x, B) = case ox of
                           NONE => (x, B)
                         | SOME y => let val y = Var.named y
                                     in (y, rename x y B) end
      in
          {subgoals = [H >> `(Eq (A, A, `(Univ level))),
                       (x, false, A) ::: H >> B],
           evidence = fn [d1, d2] => Derivation.IsectIntro (x, d1, d2)
           | _ => raise InternalError "Isect.Intro" }
      end

    (* H >> {x : A1} B1 = {x : A2} B2 in U{i}
     *     H >> A1 = A2 in U{i}
     *     H, [x : A1] >> B1 = B2 in U{i}
     *)
    fun Eq (H >> C) =
      let val (x, A1, B1, y, A2, B2, i) =
              case outof C of
                  Expr.Eq (lhs, rhs, ty) =>
                  (case (outof lhs, outof rhs, outof ty) of
                       (Isect (A1, Bind (x, B1)), Isect (A2, Bind (y, B2)), Univ i) =>
                       (x, A1, B1, y, A2, B2, i)
                     | _ => raise ExternalError "Isect.Eq expects an equality between pis in a universe")
               | _ => raise ExternalError "Isect.Eq expects an equality"
      in { subgoals = [H >> `(Expr.Eq (A1, A2, `(Univ i))),
                       (x, false, A1) ::: H >> `(Expr.Eq (B1, rename y x B2, `(Univ i)))],
           evidence = fn [d1, d2] => Derivation.IsectEq (x, d1, d2)
                              | _ => raise InternalError "Isect.Eq" }
      end
  end

  structure Univ = struct
    fun Eq (H >> C) =
      case Expr.outof C of
          Expr.Eq (lhs, rhs, ty) =>
          (case (Expr.outof lhs, Expr.outof rhs, Expr.outof ty) of
               (Expr.Univ i, Expr.Univ j, Expr.Univ k) =>
               if i <> j
               then raise ExternalError "Univ.Eq: These universes do not have the same level"
               else if i + 1 <> k
               then raise ExternalError ("Univ.Eq: Level " ^ Int.toString k ^
                                     " is not the successor of level " ^
                                     Int.toString i)
               else { subgoals = [],
                      evidence = fn _ => Derivation.UniEq i}

            | _ => raise ExternalError ("Univ.Eq expects an equality between universes " ^
                                    "in a universe, rather than " ^ Expr.toString C))
       | _ => raise ExternalError ("Univ.Eq expects an equality " ^
                               "rather than " ^ Expr.toString C)
  end

  fun wrap_level oe t =
    case oe of
        NONE => FAIL "expected level"
      | SOME e => (case Expr.outof (ExprAst.toExpr [] e) of
                       Expr.Univ i => t i
                     | _ => FAIL "level expr must be universe")
  infix ORELSE
  fun Intro oe ox =
           (wrap_level oe Pi.Intro ox)
    ORELSE (wrap_level oe Isect.Intro ox)

  fun Eq oe =
             Univ.Eq
      ORELSE wrap_level oe Pi.LamEq
      ORELSE Pi.Eq
      ORELSE Isect.Eq
      ORELSE FAIL "No applicable equality step (perhaps you forgot a 'with'?)"

  fun Elim x oe =
    FAIL "Elim is unimplemented"
end

structure TacticInterpreter = struct
  open Tactic TacticAst

  fun interpret Id = ID
    | interpret (Intro (oe, ox)) = Rules.Intro oe ox
    | interpret (Elim (x, oe)) = Rules.Elim x oe
    | interpret (Eq oe) = Rules.Eq oe
    | interpret Fail = FAIL ""
    | interpret (Then (t1, t2)) = THEN (interpret t1, interpret t2)
    | interpret (ThenL (t, l)) = THENL (interpret t, List.map interpret l)
    | interpret (OrElse (t1, t2)) = ORELSE (interpret t1, interpret t2)
    | interpret (Hyp x) = Rules.General.Hyp x
    | interpret HypEq = Rules.General.HypEq
    | interpret Reduce = Rules.General.Reduce
end

structure Refiner = struct
  datatype result = Proved of Derivation.t
                  | Incomplete of Sequent.t list
                  | Failed of string

  fun prove seq tac =
    let val {subgoals, evidence} = tac seq
    in case subgoals of
           [] => Proved (evidence [])
         | _ :: _ => Incomplete subgoals
    end
    handle Tactic.InternalError msg => Failed ("InternalError: " ^ msg)
         | Tactic.ExternalError msg => Failed msg

  fun resultToString (Proved d) = "Proved! Extract:\n" ^
                                  Expr.toString (Derivation.extract d) ^ "\n"
    | resultToString (Incomplete l) =
      "Remaining subgoals:\n" ^
      String.concatWith "\n\n" (List.map Sequent.toString l)
    | resultToString (Failed msg) = "Failed! " ^ msg
end


structure CommandInterpreter = struct
  open CommandAst

  fun interpret (Definition (x, e)) = raise Fail "definition not implemented"
    | interpret (Theorem (x, ty, tac)) =
      Refiner.prove (Sequent.ofExpr (ExprAst.toExpr [] ty)) (TacticInterpreter.interpret tac)
end

structure Main = struct
  open TextIO

  fun main (_, args) =
    let val istream =
            case args of
                [] => stdIn
             | arg :: _ => if arg = "-" then stdIn
                           else openIn arg
        val contents = inputAll istream
        val tokens = Tokenizer.tokenize contents
        (*
        val () = List.app
                  (fn (p, t) => print (Position.toString p ^ ": " ^ Token.toString t ^ "\n"))
                  tokens
        *)
        fun go (ts as (_ :: _)) =
            let val (cmd, ts) = Parser.parse_command ts
            in print ("Got command:\n" ^ CommandAst.toString cmd ^ "\n");
               print (Refiner.resultToString (CommandInterpreter.interpret cmd) ^ "\n");
               go ts
            end
          | go [] = ()
        val () = go tokens
    in
        print "done!\n"; 0
    end
    handle Parser.ParseError msg => (print ("ParseError " ^ msg ^ "\n"); 1)
        | Tokenizer.LexicalError msg => (print ("LexicalError " ^ msg ^ "\n"); 1)
        | e => (print ("Exception : " ^ exnName e ^ " " ^ exnMessage e ^ "\n"); 1)
end
