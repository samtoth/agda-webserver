module Router where

open import Prelude

open import Container.List
--open import Control.Effect renaming (Handler to EHandler)
--open import Control.Effect.Embed
open import Api

open Api.MimeUnrender {{...}}

postulate
  RouteNotFoundResponse : Response
  RouteBadBody : Response



data EndpointMatch {ℓ} : List Query → Endpoint {ℓ} → Set (lsuc ℓ) where
  verb : ∀ { status A ctypes reqMeth} → EndpointMatch [] (verb reqMeth status A ctypes)

  ¿_⦂_⟶_ : ∀ {s A} → (fe : A → Endpoint) → EndpointMatch [] (¿ s ⦂ A ⟶ fe )
  

  ReqBody⦂_∈_⟶_ : EndpointMatch {!!} {!!}

data RouteMatch {ℓ} : ∀ (a : Api {ℓ}) → List String → Set (lsuc ℓ) where
  _<∥_ : ∀ {a1 : Api {ℓ}}  {route : List String} → RouteMatch a1 route → (a2 : Api {ℓ}) →  RouteMatch (a1 ∥ a2) route
  _∥>_ : ∀ (a1 : Api {ℓ}) {a2 : Api {ℓ}}  {route : List String} → RouteMatch a2 route →  RouteMatch (a1 ∥ a2) route
  _//_ : ∀ (head : String) {a : Api {ℓ}} {routeTail : List String} → RouteMatch a routeTail → RouteMatch (head // a) (head ∷ routeTail)
  [_]//_ : ∀ {A : Set ℓ} {head : String} {apif : (A → Api {ℓ})}
             {a : A} ⦃ r : Readable A ⦄ → head is a →
             {routeTail : List String} → RouteMatch (apif a) routeTail →
             RouteMatch ([ A ]// apif) (head ∷ routeTail)
  rawMatch : ∀ (route : List String) → RouteMatch RAW route  
  endpointCollector : ∀ {end : Endpoint {ℓ}} → ((req : Request) → EndpointMatch (queryString req) end) → RouteMatch (provide end) []


endMatches? : ∀ (req : Request) (e : Endpoint {ℓ}) → Dec (EndpointMatch (queryString req) e)
endMatches? = {!!}


matches? : (a : Api {ℓ}) → (route : List String) → Request → Dec (RouteMatch a  route)
matches? (l ∥ r) route req with matches? l route req
... | yes L = yes (L <∥ r)
... | no ¬L with matches? r route req
... |     yes R = yes (l ∥> R)
... |     no ¬R = no (λ where
                       (l <∥ _) → ¬L l
                       (_ ∥> r) → ¬R r
                     )
matches? (x // a) [] _ = no (λ ())
matches? (x // a) (r ∷ rs) req with x == r
... | no P = no (λ where (a // b ) → P refl)
... | yes P rewrite P with matches? a rs req
... |         yes P₁ = yes (r // P₁)
... |         no  P₁ = no λ where (_ // b) → P₁ b


matches? ([ A ]// x) [] _ = no (λ where ())
matches? ([ A ]// x) (r ∷ rs) req with read {_} {A} r
... | a , (no ¬P)  = no (λ a → {!!})
... | a , (yes P) with matches? (x a) rs req
... |                  yes P₁ = yes ([ P ]// P₁)
... |                  no ¬P₁ = no (help P ¬P₁)
  where
    help : ∀ {a : A} (R : r is a) (¬P : RouteMatch (x a) rs → ⊥) → RouteMatch ([ A ]// x) (r ∷ rs) → ⊥
    help R ¬P ([ risa ]// b) rewrite ReadUnique R risa = ¬P b
matches? RAW r _ = yes (rawMatch r)
matches? (provide e) (_ ∷ _) _ = no (λ ())
matches? (provide e) [] req with endMatches? req e
... | yes E = yes (endpointCollector {!!})
... | no ¬E = no (λ where (endpointCollector e) → {!!})
                          


example : ∀ {Req : Request} → RouteMatch ("test" // (provide (verb GET 200 ⊤ []) ∥ provide (verb PUT 200 ⊤ []))) ("test" ∷ [])
example {req} = case (matches? ("test" // (provide (verb GET 200 ⊤ []) ∥ provide (verb PUT 200 ⊤ []))) ("test" ∷ []) req) of λ where
               (yes P) → P
               (no ¬p) → ⊥-elim (¬p (_ // (endpointCollector ({!!}) <∥ _)))



{-
generateApp : {a : Api {ℓ}} → Handler a → Application {_}
generateApp h  = λ req return → case route h (pathInfo req) req return of λ where
                                     (just x) → x
                                     nothing → return (RouteNotFoundResponse)                                   
  where
    endpointResponse : ∀ {ℓ} {e : Endpoint {ℓ}} → EndHandler e → ApplicationM {{!!}} (Maybe)
    endpointResponse (¿ s₁ ⦂ A ⟶ x) = λ _ return → {!!}
    endpointResponse (ReqBody⦂_⟶_ A {ctypes} x) = λ req cont →
      let headers = requestHeaders req
      in let failure = cont RouteBadBody
      in let contentType = filter (λ where (h , _) → fromBs h ==? "Content-Type") headers
      in case contentType of λ where
         ((_ , ct) ∷ _) → case (any? (_==? fromBs ct) (concat (map (λ where (_ , a , _) → Accept.mimeCodes a) (toList ctypes))) ) of λ where
                   true → just $ strictRequestBody req >>=′ λ bod → case (unrender {_} {_} {_} ⦃ {!!} ⦄ bod) of λ where
                           (left err) → failure
                           (right a) → case endpointResponse (x {!a!}) req cont of λ where
                             (just x) → x
                             nothing → failure
                   false → just failure 
         [] → just failure
    endpointResponse (verb v ⟶ x) = λ _ return → {!!}
    endpointResponse (RAW x) = λ req cont → just (x req cont)
  
    route : ∀ {ℓ} {a : Api {ℓ}} → Handler a → List String → ApplicationM {ℓ} Maybe
    route (respond a) s = endpointResponse a
    route h [] = λ req ret → nothing
    route (h ∥ h₁) s@(x ∷ xs) = λ req cont → (route h s req cont) <|> route h₁ s req cont
    route (path // h) (x ∷ xs) = case (path == x) of λ where
                                          (yes _) →  route h xs
                                          (no _) →  λ x₂ x₃ → nothing
    route ([ A ]// h) (x ∷ s) = route (h ({!!})) s
-}
