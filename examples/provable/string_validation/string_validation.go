package string_validation

type InvalidKeyError struct{}

func (InvalidKeyError) Error() string { return "invalid key prefix" }

//golean:verify validatesPrefix : ∀ input : ByteArray,
//golean:verify+   (∃ size : GoTypes.Int, size.toInt = input.size) →
//golean:verify+   ValidateKey input =
//golean:verify+     if 2 ≤ input.size ∧ (input.extract 0 2).data = #[120, 58] then
//golean:verify+       some (input.extract 2 input.size, none)
//golean:verify+     else some (ByteArray.mk #[], some "github.com/frederik-jatzkowski/go-lean/examples/provable/string_validation.InvalidKeyError")
func ValidateKey(s string) (string, error) {
	if len(s) < 2 || s[:2] != "x:" {
		return "", InvalidKeyError{}
	}
	return s[2:], nil
}
