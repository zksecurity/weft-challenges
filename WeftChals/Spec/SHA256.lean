import Wychelean.Hashes.SHA256
import Mathlib.Tactic.IntervalCases

/-!
# Word-vector adapters for Wychelean's SHA-256 specification

The circuit interface uses vectors of eight words. Wychelean uses a state
structure; these adapters change only the representation.
-/
namespace WeftChals.SHA256

def stateOfWords (ws : Vector UInt32 8) : Wychelean.Hashes.SHA256.State :=
  ⟨ws[0], ws[1], ws[2], ws[3], ws[4], ws[5], ws[6], ws[7]⟩

def stateWords (st : Wychelean.Hashes.SHA256.State) : Vector UInt32 8 :=
  #v[st.a, st.b, st.c, st.d, st.e, st.f, st.g, st.h]

@[simp] theorem stateOfWords_stateWords (st : Wychelean.Hashes.SHA256.State) :
    stateOfWords (stateWords st) = st := by cases st; rfl

@[simp] theorem stateWords_stateOfWords (ws : Vector UInt32 8) :
    stateWords (stateOfWords ws) = ws := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [stateWords, stateOfWords]

def roundWords (st : Vector UInt32 8) (k w : UInt32) : Vector UInt32 8 :=
  stateWords (Wychelean.Hashes.SHA256.round (stateOfWords st) k w)

def roundsWords (st : Vector UInt32 8) (W : Vector UInt32 64) : Vector UInt32 8 :=
  stateWords (Wychelean.Hashes.SHA256.rounds (stateOfWords st) W)

/-- Wychelean's compression function, with its state represented by eight words. -/
def compressWords (st : Vector UInt32 8) (block : Vector UInt32 16) : Vector UInt32 8 :=
  stateWords (Wychelean.Hashes.SHA256.compress (stateOfWords st) block)

end WeftChals.SHA256
