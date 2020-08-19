import string
from random import sample

class PasswordGenerator:
    def __init__(self, ud : bool, us : bool, pswd_len="6"):
        self.use_digit = ud
        self.use_symbols = us
        self.pswd_len = int(pswd_len)
        self.symbols = set(string.ascii_lowercase)

    def generate(self):
        self._fill_symbols()
        password = ""
        for i in range(self.pswd_len):
            password += sample(self.symbols, 1)[0]
        
        return password

    def _fill_symbols(self):
        if (self.use_digit):
            self.symbols = self.symbols.union(set(string.digits))
        
        if (self.use_symbols):
            self.symbols = self.symbols.union(set("!?$#%"))