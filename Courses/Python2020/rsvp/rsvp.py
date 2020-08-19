import os
from tkinter import *

class TextIterator():
    def __init__(self, txt):
        self._text = txt.split()
        self._curr_word = -1

    def next(self):
        self._curr_word += 1
        try:
            return self._text[self._curr_word]
        except (IndexError, ValueError):
            return 'Text end'

    def prev(self):
        self._curr_word -= 1
        try:
            return self._text[self._curr_word]
        except (IndexError, ValueError):
            return 'Out of text range'

class RSVPReader():
    def __init__(self, parent, text_file, wpm=300):
        self.text_iterator = TextIterator(self.text_loader(text_file))
        self._wpm = wpm
        self.speed = self.calc_speed()
        self.active = False

        self.tk = Toplevel(parent)
        self.info = StringVar()
        self.tk.title(text_file)
        self.tk.geometry('700x150')

        self.label = Label(self.tk, textvariable=self.info, font=('Helvetica', 34))
        self.info.set("Press Space for start/stop")
        self.label.pack()
    
        self.msg = Message(self.tk, text="wpm: " + str(self._wpm))
        self.msg.config()
        self.msg.pack() 

        self.button = Button(self.tk, text='Exit', width=25, command=self.tk.destroy)
        self.button.pack()

        self.tk.bind('<Key>', self.keypress)
        self.tk.mainloop()

    def text_loader(self, text_file):
        with open(text_file, 'r') as f:
            return f.read()

    def get_next(self):
        word = self.text_iterator.next()
        self.info.set(word)
    
    def get_pred(self):
        word = self.text_iterator.prev()
        self.info.set(word)

    def calc_speed(self):
        return int(60000 / self._wpm)

    def reader(self):
        if self.active:
            self.get_next()
            self.tk.after(self.speed, self.reader)

    def keypress(self, event):
        if event.keycode == 65:
            self.active = not (self.active)
            self.process_space()
        elif event.keycode == 111:
            self.process_uparrow()
        elif event.keycode == 116:
            self.process_downarrow()
        elif not (self.active):
            if event.keycode == 113:
                self.process_leftarrow()
            elif event.keycode == 114:
                self.process_rightarrow()

    def process_space(self):
        self.reader()

    def process_downarrow(self):
        self.speed_down()

    def process_uparrow(self):
        self.speed_up()

    def process_leftarrow(self):
        self.get_pred()

    def process_rightarrow(self):
        self.get_next()

    def speed_down(self):
        self.change_wpm(-10)

    def speed_up(self):
        self.change_wpm(10)

    def change_wpm(self, delta_wpm):
        self._wpm += delta_wpm
        self.speed = self.calc_speed()
        self.msg.config(text="wpm: " + str(self._wpm))


class TextMenu():
    def __init__(self, text_dir, wpm=300):
        self.texts = os.listdir(text_dir)
        self.default_wpm = wpm

        self.tk = Tk()
        self.tk.title("Menu")
        self.tk.geometry('700x900')
        buttons = []

        for t in self.texts:
            text_name = os.path.splitext(t)[0]
            b = Button(self.tk,
                    text=text_name,
                    command=lambda text_name=text_name: self.open_text(text_dir + "/" + text_name + ".txt"))
            b.pack()

        self.tk.mainloop()

    def open_text(self, filename):
        self.cur_text = RSVPReader(self.tk, filename, self.default_wpm)


if __name__ == "__main__":
    t = TextMenu('testdir', wpm=400)
