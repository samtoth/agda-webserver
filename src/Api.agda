module Api where

open import Prelude
open import Agda.Builtin.Sigma

variable
 ℓ : Level

postulate
  ByteString : Set
  fromBs : ByteString → String
  Settings : Set
  Response : Set
  emptyResponse : Response
  
Header : Set
Header = ByteString × ByteString

Query : Set
Query = ByteString × Maybe ByteString

data Verb : Set where
  GET : Verb
  POST : Verb
  PUT : Verb
  DELETE : Verb
  PATCH : Verb
  
postulate
  Request : Set
  pathInfo : Request → List String
  requestHeaders : Request → List Header
  requestMethod : Request → Verb
  queryString : Request → List Query
  strictRequestBody : Request → IO ByteString
 

Application : Set (lsuc ℓ)
Application {l} = Request → (∀ {A : Set l} → (Response → IO A) → IO A) 

ApplicationM : (Set ℓ → Set ℓ) → Set (lsuc ℓ)
ApplicationM {l} M = Request → ∀ {A : Set l} → (Response → IO A) → M (IO A)


postulate
  runSettings : Settings → Application {ℓ} → IO ⊤


StatusCode : Set
StatusCode = Nat

infix 10 _∥_
infixr 15 _//_
infix 60 ReqBody⦂_⟶_

record NonEmpty (A : Set ℓ) : Set (ℓ) where
  constructor _∷_
  field
    init : A
    tail : List A
toList : ∀ {A : Set ℓ} → NonEmpty A → List A
toList (init ∷ tail) = init ∷ tail

record Accept (ctype : Set ℓ) : Set (lsuc ℓ) where
  field
    mimeCodes : List String

record MimeRender {ctype : Set ℓ} ⦃ _ : (Accept ctype) ⦄ (A : Set ℓ) : Set (lsuc ℓ) where
  field
    render : A → ByteString

record MimeUnrender {ctype : Set ℓ} ⦃ _ : (Accept ctype) ⦄ (A : Set ℓ) : Set (lsuc ℓ) where
  field
    unrender : ByteString → Either String A


ctypeMR : ∀ (A : Set ℓ) → Set (lsuc ℓ)
ctypeMR {l} A = Σ (Set l) (λ ctype → Σ (Accept ctype) λ accept → MimeRender ⦃ accept ⦄ A)

ctypeMUr : ∀ (A : Set ℓ) → Set (lsuc ℓ)
ctypeMUr {l} A = Σ (Set l) (λ ctype → Σ (Accept ctype) λ accept → MimeUnrender ⦃ accept ⦄ A)

record Readable (A : Set ℓ) : Set (lsuc ℓ) where
  field
    _is_ : String → A → Set ℓ
    read : (s : String) → Σ A (λ a → Dec (s is a))
    ReadUnique : ∀ {s a a'} → s is a → s is a' → a ≡ a'
    
open Readable {{...}} public

data Endpoint {ℓ : Level} : Set (lsuc ℓ) where
  ¿_⦂_⟶_ : String → (A : Set ℓ) → (A → Endpoint {ℓ}) → Endpoint
  ReqBody⦂_∈_⟶_ : (Bod : Set ℓ) → (_ : NonEmpty (ctypeMUr Bod)) → Endpoint {ℓ} → Endpoint 
  verb : Verb → StatusCode → (A : Set ℓ) → List (ctypeMR A) → Endpoint

data Api {ℓ : Level} : Set (lsuc ℓ) where
  _∥_ : Api {ℓ} → Api {ℓ} → Api
  _//_ : String → Api {ℓ} → Api
  [_]//_ : (A : Set ℓ) → ⦃ _ : Readable A ⦄ → (A → Api {ℓ}) → Api
  provide : Endpoint {ℓ}→ Api 
  RAW : Api

data EndHandler {ℓ} : Endpoint {ℓ} → Set (lsuc ℓ) where
  ¿_⦂_⟶_ : ∀ {e : Endpoint {ℓ}} ( s : String) → (A : Set ℓ) → (A → EndHandler e) → EndHandler (¿ s ⦂ A ⟶ const e)
  ReqBody⦂_⟶_ : ∀ (A : Set ℓ) {ctypes : NonEmpty (ctypeMUr A)} {e : Endpoint} → (A → EndHandler e) → EndHandler (ReqBody⦂ A ∈ ctypes  ⟶ e)
  verb_⟶_ : ∀ (v : Verb) {code : StatusCode} {Return : Set ℓ} {ctypes : List (ctypeMR Return)} → IO Return → EndHandler (verb v code Return ctypes) 



data Handler {ℓ} : Api {ℓ} → Set (lsuc ℓ) where
  _∥_ : ∀ {a b : Api {ℓ}} → Handler a → Handler b → Handler (a ∥ b) 
  _//_ : ∀ {a : Api {ℓ}} → (s : String) → Handler a → Handler (s // a) 
  [_]//_ : ∀ (A : Set ℓ) → ⦃ _ : Readable A ⦄ → {apif : A → Api {ℓ}} → ((a : A) → Handler (apif a)) → Handler ([ A ]// apif)
  respond : ∀ {e : Endpoint} → EndHandler e → Handler (provide e)
  RAW : Application {ℓ} → Handler RAW 

capture : ∀  (A : Set ℓ) → ⦃ _ : Readable A ⦄ → {apif : A → Api {ℓ}} → ((a : A) → Handler (apif a)) → Handler ([ A ]// apif)
capture = [_]//_

--infixr 12 [_⦂_]//_
syntax capture a (λ x → t) = [ x ⦂ a ]// t

fromBody : ∀ (A : Set ℓ) {ctypes : NonEmpty (ctypeMUr A)} {e : Endpoint} → (A → EndHandler e) → Handler (provide (ReqBody⦂ A ∈ ctypes  ⟶ e))
fromBody A handle = respond (ReqBody⦂ A ⟶ handle)

--infixr 12 given_⦂_⟶_
syntax fromBody A (λ a → e) = given a ⦂ A ⟶ e

constCtype : ∀ {A : Set} → A → Set
constCtype _ = ⊤

instance
  constCtypeA : ∀ {A} → {a : A} →  Accept (constCtype a)
  constCtypeA .Accept.mimeCodes = [ "const" ]

  constCtypeUnrender : ∀ {A} → {a : A} → MimeUnrender ⦃ constCtypeA {_} {a} ⦄ A
  constCtypeUnrender {_} {a} .MimeUnrender.unrender = const (right a)

content : (C : Set) → {A : Set} → ⦃ acpt : Accept C ⦄ → ⦃ _ : MimeUnrender ⦃ acpt ⦄ A ⦄ → ctypeMUr A
content C  ⦃ acpt ⦄ ⦃ mr ⦄ = (C , acpt , mr)


ctypeWoo : ctypeMUr String
ctypeWoo = content (constCtype woohoo) {_} ⦃ constCtypeA {_} {woohoo} ⦄ ⦃ constCtypeUnrender {_} {woohoo} ⦄
  where
    woohoo : String
    woohoo = "woohoo"

instance
  postulate
    readableNat' : Readable Nat
  readableℕ : Readable Nat
  readableℕ = readableNat'

myTestApi : Api
myTestApi = "users" // [ Nat ]// (λ _ → provide (ReqBody⦂ String ∈ (ctypeWoo ∷ []) ⟶ verb GET 200 String []))
            ∥ RAW


myHandler : Handler myTestApi
myHandler =    "users" // [ userid ⦂ Nat ]// given req ⦂ String ⟶ (verb GET ⟶ return req )
             ∥ (RAW (λ req return → return emptyResponse))




