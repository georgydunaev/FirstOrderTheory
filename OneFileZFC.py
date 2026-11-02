def MembershipOnly(elem, collection):
    """Check membership in a list representation of a finite ZFC set."""
    if not isinstance(collection, list):
        raise TypeError("MembershipOnly expects a list as the second argument")
    return elem in collection
