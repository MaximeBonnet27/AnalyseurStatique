(* Domaine des intervalles *)

open Abstract_syntax_tree
open Value_domain

module Intervals = (struct

(* Une borne est soit une constante soit un infini *)

type borne =
        Cst of Z.t
        | POS_INF
        | NEG_INF

(* TODO donner un nom aux bornes ? *)


type intervalle =
        | INTER of borne * borne
        | BOT
        | TOP


(* Utils *)

let max borneA borneB =
        match borneA, borneB with
        | POS_INF, _ | _, POS_INF -> POS_INF
        | NEG_INF, x | x, NEG_INF -> x
        | Cst x, Cst y ->
                if x > y then Cst x else Cst y


let min borneA borneB =
        match borneA, borneB with
        | NEG_INF, _ | _, NEG_INF -> NEG_INF
        | POS_INF, x | x, POS_INF -> x
        | Cst x, Cst y ->
                if x < y then Cst x else Cst y

let gt_zero borne =
        match borne with
        | Cst x -> x > Z.zero
        | POS_INF -> true
        | NEG_INF -> false

let lt_zero borne = not (gt_zero borne)

let add_one borne =
        match borne with
        | Cst x -> Cst (Z.add x Z.one)
        | _ -> borne

let sub_one borne =
        match borne with
        | Cst x -> Cst (Z.sub x Z.one)
        | _ -> borne

let print_borne borne =
        match borne with
        | Cst x -> Z.to_string x
        | POS_INF -> "+oo"
        | NEG_INF -> "-oo"

let neg_borne borne =
        match borne with
        | Cst x -> Cst (Z.neg x)
        | POS_INF -> NEG_INF
        | NEG_INF -> POS_INF

let add_bornes borneA borneB =
        match borneA, borneB with
        | Cst x, Cst y -> Cst (Z.add x y)
        (* POS_INF est prioritaire par rapport à NEG_INF *)
        (* Mais on ne devrait pas avoir à les additioner *)
        | POS_INF, x | x, POS_INF -> POS_INF
        | NEG_INF, x | x, NEG_INF -> NEG_INF


let sub_bornes borneA borneB =
        match borneA, borneB with
        | Cst x, Cst y -> Cst (Z.sub x y)
        (* POS_INF est prioritaire par rapport à NEG_INF *)
        (* Mais on ne devrait pas avoir à les additioner *)
        | POS_INF, x | x, NEG_INF -> POS_INF
        | NEG_INF, x | x , POS_INF -> NEG_INF

let mul_bornes borneA borneB =
        match borneA, borneB with
        | Cst x, Cst y -> Cst (Z.mul x y)
        | NEG_INF, POS_INF | POS_INF, NEG_INF -> NEG_INF
        | NEG_INF, NEG_INF -> POS_INF
        | POS_INF, Cst x | Cst x, POS_INF ->
                if x = Z.zero then Cst Z.zero
                else if x < Z.zero then NEG_INF else POS_INF
        | NEG_INF, Cst x | Cst x, NEG_INF ->
                if x = Z.zero then Cst Z.zero
                else if x > Z.zero then NEG_INF else POS_INF
        | POS_INF, POS_INF -> POS_INF


(* Le cas ou l'une des bornes est nulle est déjà traitée dans apply_diff_zero *)
let div_bornes borneA borneB =
        match borneA, borneB with
        | Cst x, Cst y -> Cst (Z.div x y)
        | _, POS_INF | _, NEG_INF -> Cst(Z.zero)
        | POS_INF, Cst x -> if x < Z.zero then NEG_INF else POS_INF
        | NEG_INF, Cst x -> if x > Z.zero then NEG_INF else POS_INF

let erem_bornes borneA borneB =
        match borneA, borneB with
        | Cst x, Cst y -> Cst(Z.erem x  y)
        | Cst x, POS_INF -> Cst x
        | Cst x, NEG_INF -> Cst(Z.neg  x)



(* Implémentation de l'interface *)

type t = intervalle

let top = TOP (*intervalle NEG_INF POS_INF*)

let bottom = BOT

let const c = INTER (Cst c, Cst c)

let rand x y =
        if x = y then const x
        else if x < y then INTER (Cst x, Cst y)
        else BOT

(* intersection *)
let meet intervalleA intervalleB =
        match intervalleA, intervalleB with
        | BOT, _ | _, BOT -> BOT
        | x, TOP | TOP, x -> x
        | INTER (a,b), INTER (c, d) ->
        (* Ensembles disjoints *)
        if (a < c && b < c) || (c < a && d < a) then
                BOT
        else
                INTER ((max a c),(min b d))

(* union *)
let join intervalleA intervalleB =
        match intervalleA, intervalleB with
        | TOP, _ | _, TOP -> TOP
        | BOT, x | x, BOT -> x
        | INTER (a, b), INTER (c, d) -> INTER ((min a c), (max b d))

(* TODO *)
let subset intervalleA intervalleB =
        match intervalleA, intervalleB with
        | BOT,_ | _,TOP -> true
        | INTER (a, b), INTER (c, d) -> a >= c && b <= d
        | _ -> false

let is_bottom x =
        x = BOT

let print format inter = match inter with
        | BOT -> Format.fprintf format "bottom"
        | TOP -> Format.fprintf format "top"
        | INTER (x, y) -> Format.fprintf format "[%s,%s]" (print_borne x) (print_borne y)


(* OPERATIONS ARITHMETIQUES *)

let neg inter =
        match inter with
        | INTER(a, b) -> INTER(neg_borne b, neg_borne a)
        | TOP -> TOP
        | BOT -> BOT

let add interA interB =
        match interA, interB with
        | BOT , _  | _, BOT -> BOT
        | TOP , _ | _, TOP -> TOP
        | INTER(a, b), INTER(c, d) -> INTER(add_bornes a c, add_bornes b d)


let sub interA interB =
        match interA, interB with
        | BOT , _  | _, BOT -> BOT
        | TOP , _ | _, TOP -> TOP
        | INTER(a, b), INTER(c, d) -> INTER(sub_bornes a d, sub_bornes b c)


let mul interA interB =
        match interA, interB with
        | BOT , _  | _, BOT -> BOT
        | TOP , _ | _, TOP -> TOP
        | INTER(a, b), INTER(c, d) ->
                let ac = mul_bornes a c in
                let ad = mul_bornes a d in
                let bc = mul_bornes b c in
                let bd = mul_bornes b d in
                let borne_inf = min (min ac ad) (min bc bd) in
                let borne_max = max (max ac ad) (max bc bd) in
                INTER(borne_inf, borne_max)

let div interA interB =
        match interA, interB with
        | BOT , _  | _, BOT -> BOT
        | TOP , _ | _, TOP -> TOP
        | INTER (_, _), INTER(Cst x, _)
        | INTER (_, _), INTER(_, Cst x) when x = Z.zero -> BOT
        | INTER(a, b), INTER(c, d) ->
                let ac = div_bornes a c in
                let ad = div_bornes a d in
                let bc = div_bornes b c in
                let bd = div_bornes b d in
                let borne_inf = if gt_zero c then
                        min ac ad else min bc bd in
                let borne_sup = if gt_zero c then
                        max bc bd else max ac ad in
                INTER(borne_inf, borne_sup)


(* TODO *)
let erem interA interB = TOP

(* FILTRES *)

(* Testé ! *)
let eq interA interB =
        match interA, interB with
        (* x x ? *)
        | TOP, x | x, TOP -> x, x
        | BOT, _ | _, BOT -> BOT, BOT
        | _ -> let intersection = meet interA interB in
                intersection, intersection

(* Ca devrait être bon *)
let neq interA interB =
        match interA, interB with
        | TOP, x | x, TOP
        | BOT, x | x, BOT -> interA, interB
        | INTER(a, b), INTER(c, d) ->
        (* Premier intervalle est une constante *)
        if a = b then
                (* Si l'autre intervalle est une constante également *)
                if c = d then
                        (* On compare les deux constantes *)
                        if a = c then
                                BOT, BOT
                        else
                                interA, interB
                (* Si la constante est l'une des deux bornes de l'autre intervalle *)
                else if a = c then
                        interA, INTER(add_one c, d)
                else if a = d then
                        interA, INTER(c, sub_one d)
                else
                        interA, interB
        (* Deuxième intervalle est une constante *)
        else if c = d then
                if c = a then
                        INTER(add_one a, b), interB
                else if c = b then
                        INTER(a, sub_one b), interB
                else
                        interA, interB
        (* Si deux intervalles, on ne peut pas les filtrer *)
        else
                interA, interB

(* BON ? *)
let geq interA interB =
        match interA, interB with
        | BOT, _ | _, BOT
        | TOP, TOP -> interA, interB
        | TOP, INTER(a, b) -> INTER(a, POS_INF), INTER(a, b)
        | INTER(a, b), TOP -> INTER(a, b), INTER(NEG_INF, b)
        | INTER(a, b), INTER(c, d) ->
                (* Tout le premier intervalle est inférieur au deuxieme *)
                if b < c then
                        BOT, BOT
                (* c entre a et b *)
                else
                let borne_sup = min b d in
                if c >= a && b >= c then
                        INTER(c, b), INTER(c, borne_sup)
                else
                        interA, INTER(c, borne_sup)

(* Première version (y) *)
let gt interA interB =
        match interA, interB with
        | BOT, _ | _, BOT -> interA, interB
        | _, TOP -> BOT, BOT
        | TOP, INTER(a, b) -> INTER(add_one b, POS_INF), INTER(a, b)
        | INTER(a, b), INTER(c, d) ->
        (* Tout le premier intervalle est inférieur au deuxieme *)
        if b < c then
                BOT, BOT
        else
                (* c entre a et b *)
                if c >= a && b > c then
                        if c = d then
                                INTER(add_one c, b), INTER(c, c)
                        else
                                INTER(add_one c, b), INTER(c, c)
                else
                        if b = d then
                                BOT, BOT
                        else
                                interA, INTER(c, max c (sub_one b) )


let bwd_unary inter op r =
        match op with
        | AST_UNARY_PLUS -> meet inter r
        | AST_UNARY_MINUS -> meet inter (neg r)

let bwd_binary x y op r =
        match op with
        | AST_PLUS     -> meet x (sub r y), meet y (sub r x)
        | AST_MINUS    -> meet x (add r y), meet y (sub x r)
        | AST_MULTIPLY -> meet x (div r y), meet y (div r x)
        | AST_DIVIDE   ->
                let intervalle_uns = INTER(Cst (Z.neg Z.one), Cst Z.one) in
                let s = add r intervalle_uns in
                meet x (mul s x), meet y (join (div x s) (const Z.zero))
        (* TODO *)
        | AST_MODULO   -> x, y

(* TODO *)
let widen = join


let unary inter op = match op with
        | AST_UNARY_PLUS  -> inter
        | AST_UNARY_MINUS -> neg inter

let binary interA interB op = match op with
        | AST_PLUS     -> add interA interB
        | AST_MINUS    -> sub interA interB
        | AST_MULTIPLY -> mul interA interB
        | AST_DIVIDE   -> div interA interB
        | AST_MODULO   -> erem interA interB

let compare interA interB op = match op with
        | AST_EQUAL         -> eq interA interB
        | AST_NOT_EQUAL     -> neq interA interB
        | AST_GREATER_EQUAL -> geq interA interB
        | AST_GREATER       -> gt interA interB
        | AST_LESS_EQUAL    -> let interB',interA' = geq interB interA in interA',interB'
        | AST_LESS          -> let interB',interA' = gt interB interA in interA',interB'



end : VALUE_DOMAIN)
