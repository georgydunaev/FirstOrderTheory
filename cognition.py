class Terms:
    pass

def FVC(sv):
    return {'type': 'FVC', 'value': sv}

def FSC(f, v):
    return {'type': 'FSC', 'function': f, 'args': v}

def term_substitution(t1, t2, x):
    if t1['type'] == 'FVC' and t1['value'] == x:
        return t2
    elif t1['type'] == 'FSC':
        return FSC(t1['function'], [term_substitution(arg, t2, x) for arg in t1['args']])
    else:
        return t1