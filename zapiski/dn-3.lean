set_option autoImplicit false

/------------------------------------------------------------------------------
 ## Naravna števila

 Definirajte funkcijo, ki _rekurzivno_ (torej naivno in ne direktno s formulo,
 ki jo boste morali dokazati) sešteje prvih `n` naravnih števil, ter
 dokažite, da zanjo velja znana enakost (najprej v obliki, ki ne zahteva
 deljenja, nato pa še v običajni obliki).
------------------------------------------------------------------------------/

def vsota_prvih : Nat → Nat :=
  fun n =>
    match n with
    | .zero => 0
    | .succ n => vsota_prvih n + (n+1)

#eval vsota_prvih 7

theorem gauss : (n : Nat) → 2 * vsota_prvih n = n * (n + 1) :=
  by
    intro n
    induction n with
    | zero =>
      simp [vsota_prvih]
    | succ n ih =>
      simp [vsota_prvih, Nat.mul_add]
      rw [ih]
      simp [Nat.two_mul, Nat.add_mul, Nat.mul_add]
      simp [<- Nat.add_add_add_comm, Nat.add_comm]
      simp [<- Nat.add_assoc]
      simp [Nat.add_comm]



theorem cisto_pravi_gauss : (n : Nat) → vsota_prvih n = (n * (n + 1)) / 2 :=
  by
    intro n
    induction n with
    | zero =>
      simp [vsota_prvih]
    | succ n ih =>
      rw [<- gauss]
      simp


/------------------------------------------------------------------------------
 ## Vektorji

 Definirajmo vektorje podobno kot na predavanjih, le da namesto svojih naravnih
 števil uporabimo vgrajena. Da se tipi ujamejo, funkcijo stikanja napišemo s
 pomočjo taktik.

 Napišite funkcijo `obrni`, ki vrne na glavo obrnjen vektor, ter funkciji
 `glava` in `rep`, ki varno vrneta glavo in rep _nepraznega_ seznama.
------------------------------------------------------------------------------/

inductive Vektor : Type → Nat → Type where
  | prazen : {A : Type} → Vektor A 0
  | sestavljen : {A : Type} → {n : Nat} → A → Vektor A n → Vektor A (n + 1)
deriving Repr

def stakni : {A : Type} → {m n : Nat} → Vektor A m → Vektor A n → Vektor A (m + n) :=
  fun xs ys => match xs with
  | .prazen => by rw [Nat.add_comm]; exact ys
  | .sestavljen x xs' => by rw [Nat.add_right_comm]; exact Vektor.sestavljen x (stakni xs' ys)

def obrni : {A : Type} → {n : Nat} → Vektor A n → Vektor A n :=
  fun xs => match xs with
  | Vektor.prazen => Vektor.prazen
  | Vektor.sestavljen x xs' => stakni (obrni xs') (Vektor.sestavljen x (Vektor.prazen))

#eval obrni (Vektor.sestavljen 3 (Vektor.sestavljen 5 (Vektor.sestavljen 99 Vektor.prazen)))



def glava {A : Type} {n : Nat} : Vektor A n → Option A :=
  fun vekt => match vekt with
  | Vektor.prazen => Option.none
  | Vektor.sestavljen x xs => Option.some x

def rep {A : Type} {n : Nat} : Vektor A n → Option (Vektor A (n - 1)) :=
  fun vekt => match vekt with
  | Vektor.prazen => Option.none
  | Vektor.sestavljen x xs => Option.some xs


#eval glava (Vektor.sestavljen 3 (Vektor.prazen))

/------------------------------------------------------------------------------
 ## Predikatni račun

 Dokažite spodnje tri trditve. Zadnja je _paradoks pivca_, ki pravi:
   "V vsaki neprazni gostilni obstaja gost, za katerega velja,
   da če pije on, pijejo vsi v gostilni."
 Za dokaz potrebujete klasično logiko, torej nekaj iz modula `Classical`.
------------------------------------------------------------------------------/

theorem forall_implies : {A : Type} → {P Q : A → Prop} →
  (∀ x, (P x → Q x)) → (∀ x, P x) → (∀ x, Q x) :=
    by
    intros A P Q
    intros h k x
    exact h x (k x)


theorem forall_implies' : {A : Type} → {P : Prop} → {Q : A → Prop} →
  (∀ x, (P → Q x)) ↔ (P → ∀ x, Q x) :=
  by
  intros A P Q
  apply Iff.intro
  . intros h p x
    exact  h x p
  . intros h x p
    exact h p x



theorem paradoks_pivca :
  {G : Type} → {P : G → Prop} →
  (g : G) →  -- (g : G) pove, da je v gostilni vsaj en gost
  ∃ (p : G), (P p → ∀ (x : G), P x) :=
  by
    intros G P g
    apply Classical.byCases
    . intro p?
      exists g

    . intro samo_pivec

      have ne_pijejo_vsi : ¬∀(a : G), P a :=
      by
        intro vsi
        apply samo_pivec
        intro pivec
        exact vsi

      have en_ne_pije : ∃(b : G), ¬P b :=
      by
        apply Classical.not_forall.mp
        exact ne_pijejo_vsi

      have ⟨ p, ne_Pp ⟩ := en_ne_pije

      exists p
      intro Pp
      apply Classical.byContradiction
      -- apply ne_pijejo_vsi ???
      intro isto_kot_npv
      exact ne_Pp Pp


    -- cases Classical.em (∃ x : G, ¬P x) with
    --   | inl en_ne_pije =>

    --     -- have h := en_ne_pije
    --     -- cases h with
    --     -- | intro p ne_Pp =>
    --     --   exact ⟨p, fun Pp => absurd Pp ne_Pp⟩

    --     obtain ⟨p, ne_Pp⟩ := en_ne_pije
    --     exact ⟨p, fun Pp => absurd Pp ne_Pp⟩
    --   | inr vsi_pijejo =>
    --     exact ⟨g, fun _ x => Classical.byContradiction (fun ne_Px => vsi_pijejo ⟨x, ne_Px⟩)⟩





/------------------------------------------------------------------------------
 ## Dvojiška drevesa

 Podan naj bo tip dvojiških dreves skupaj s funkcijama za zrcaljenje in izračun
 višine ter dvema funkcijama, ki obe od leve proti desni naštejeta elemente
 drevesa. Pri tem prva deluje naivno in ima časovno zahtevnost O(n log n), druga
 pa je malo bolj zapletena in deluje v času O(n). Dokažite spodnje enakosti, pri
 čemer lahko do pomožne funkcije `aux` dostopate kot `elementi'.aux`
-------------------------------------------------------------------------------/

inductive Drevo : Type → Type where
  | prazno : {A : Type} → Drevo A
  | sestavljeno : {A : Type} → Drevo A → A → Drevo A → Drevo A

def zrcali : {A : Type} → Drevo A → Drevo A :=
  fun t => match t with
  | .prazno => .prazno
  | .sestavljeno l x d => .sestavljeno (zrcali d) x (zrcali l)

def visina : {A : Type} → Drevo A → Nat :=
  fun t => match t with
  | .prazno => 0
  | .sestavljeno l _ d => 1 + max (visina l) (visina d)

def elementi : {A : Type} → Drevo A → List A :=
  fun t => match t with
  | .prazno => []
  | .sestavljeno l x d => elementi l ++ x :: elementi d

def elementi' : {A : Type} → Drevo A → List A :=
  let rec aux : {A : Type} → Drevo A → List A → List A :=
    fun t acc => match t with
    | .prazno => acc
    | .sestavljeno l x d => aux l (x :: aux d acc)
  fun t => aux t []

theorem zrcali_zrcali :
  {A : Type} → (t : Drevo A) →
  zrcali (zrcali t) = t := by
  intro A t
  induction t with
    | prazno =>
      simp [zrcali]
    | sestavljeno l v r ihl ihr =>
      simp [zrcali]
      rw [ihl, ihr]
      apply And.intro
      rfl
      rfl



theorem visina_zrcali :
  {A : Type} → (t : Drevo A) →
  visina (zrcali t) = visina t := by
  intro A t
  induction t with
    | prazno =>
      simp [zrcali]
    | sestavljeno l v r ihl ihr =>
      simp [visina]
      rw [ihl, ihr]
      rw [Nat.max_comm]



theorem pomozna_trd : ∀ {A : Type}, ∀ {t : Drevo A}, ∀ {sez : List A},
  elementi'.aux t sez = elementi t ++ sez :=
by
  intro A t
  induction t with
  | prazno =>
    simp [elementi, elementi'.aux]
  | sestavljeno l x r ihl ihr =>
    simp [elementi, elementi'.aux]
    intro sez
    rw [ihr, ihl]



theorem elementi_elementi' :
  {A : Type} → (t : Drevo A) →
  elementi t = elementi' t := by
  intro A t
  induction t with
    | prazno  =>
      simp [elementi, elementi', elementi'.aux]
    | sestavljeno l x r _ _ =>
      simp [elementi']
      rw [pomozna_trd]
      simp
