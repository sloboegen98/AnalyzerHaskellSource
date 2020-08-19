import re
import random

from statistics import mean
from itertools import count

from flask import Flask
from flask import render_template
from flask import url_for
from flask import request
from flask import redirect

from genPassword import PasswordGenerator


app = Flask(__name__, static_folder='static')


@app.route('/', methods=['GET', 'POST'])
def index():
    if request.method == 'POST':
        pg = PasswordGenerator(request.form.get("digitChecker") == 'on',
                               request.form.get("symbolChecker") == 'on',
                               request.form.get("pswdLength"))

        # pg = PasswordGenerator(bool(random.getrandbits(1)),
        #                        bool(random.getrandbits(1)),
        #                        random.randrange(1, 20))

        return render_template('index.html', password=pg.generate())

    return render_template('index.html')



@app.route('/about')
def about(name=None):
    return render_template('about.html', name=name)

