# Test Suite for FirstOrderTheory

# Import necessary modules and functions from the main codebase
from FirstOrderTheory import Terms, FSV, Vector

# Define test cases for each function and module in the codebase
def test_terms_ind():
    # Test the Terms_ind theorem
    # Create a simple term and verify that the theorem holds
    term = Terms.FVC("x")
    assert Terms_ind(lambda t: True, lambda sv: True, lambda f, v, ih: True, term)

def test_term_substitution():
    # Test the term_substitution lemma
    # Create two simple terms and a variable, then verify that substitution works correctly
    term1 = Terms.FVC("x")
    term2 = Terms.FVC("y")
    var = "x"
    result = term_substitution(term1, term2, var)
    assert result == Terms.FVC("y")

# Run the test suite and verify that all tests pass
if __name__ == "__main__":
    test_terms_ind()
    test_term_substitution()
