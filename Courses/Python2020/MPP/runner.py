from antlr4.FileStream import FileStream
from antlr4.CommonTokenStream import CommonTokenStream
from antlr4.tree.Trees import Trees

from parser.MPPLexer import MPPLexer
from parser.MPPParser import MPPParser
from parser.MPPBaseLexer import MPPBaseLexer

from utils.msword import DocxExecutor
from utils.web import UrlExecutor

import sys


class Runner():

    def __init__(self, filename):
        input              = FileStream(filename, encoding='utf-8')
        lexer              = MPPLexer(input)
        stream             = CommonTokenStream(lexer)
        parser             = MPPParser(stream)
        self.start_rule    = parser.script()
        # print(Trees.toStringTree(self.start_rule, None, parser))
        self.document      = DocxExecutor()
        # like as generator
        self.cur_url_index = 0
        self.url           = None

    def run(self):
        self.run_script(self.start_rule)
        self.document.save_doc()

    def run_script(self, script_ctx):
        instrs = script_ctx.seq_instrs().instr_semi()
        for instr in instrs:
            self.run_instr(instr)

    def run_instr(self, instr_ctx):
        dinst = instr_ctx.docx_instr_semi()
        winst = instr_ctx.web_instr_semi()

        if dinst != None:
            if dinst.docx_instr() != None:
                self.run_docx_instr(dinst.docx_instr())
        
        if winst != None:
            if winst.web_instr() != None:
                self.run_web_instr(winst.web_instr())

    def run_docx_instr(self, dinstr_ctx, cur_index=-1):
        if cur_index == -1:
            cur_index = self.cur_url_index

        if dinstr_ctx.create_doc() != None:
            self.create_doc(dinstr_ctx.create_doc())
        elif dinstr_ctx.add_page() != None:
            self.add_page()
        elif dinstr_ctx.add_header() != None:
            self.add_header(dinstr_ctx.add_header())
        elif dinstr_ctx.add_text() != None:
            self.add_text(dinstr_ctx.add_text())
        elif dinstr_ctx.add_subheader() != None:
            self.add_subheader(dinstr_ctx.add_subheader())
        elif dinstr_ctx.set_orientation() != None:
            self.set_orientation(dinstr_ctx.set_orientation())
        elif dinstr_ctx.add_content() != None:
            self.add_content(dinstr_ctx.add_content(), cur_index)

    def create_doc(self, doc_ctx):
        docname = doc_ctx.getText()[2:-1].replace('+', '')
        self.document.set_name(docname)

    def add_page(self):
        self.document.create_page()

    def add_text(self, text_ctx):
        self.document.add_text(text_ctx.CommonWord().getText()[1:-1])

    def add_header(self, header_ctx):
        self.document.add_heading(header_ctx.CommonWord().getText()[1:-1])

    def add_subheader(self, sh_ctx):
        self.document.add_subheading(sh_ctx.CommonWord().getText()[1:-1])

    def set_orientation(self, orient_ctx):
        if orient_ctx.Landscape() != None:
            self.document.set_orientation('L')
        elif orient_ctx.Portrait() != None:
            self.document.set_orintation('P')

    def add_content(self, content_ctx, ind=-1):
        if ind == -1:
            ind = self.cur_url_index

        if content_ctx.Number() != None:
            ind = int(content_ctx.Number().getText())

        if content_ctx.img_or_caption().Image() != None:
            self.add_image(index=ind)
        elif content_ctx.img_or_caption().Capture() != None:
            self.add_capture(index=ind)
        elif content_ctx.img_or_caption().Full() != None:
            self.add_image(index=ind)
            self.add_capture(index=ind)
        
        self.cur_url_index += 1        

    def add_image(self, index : int):
        print("Inserting " + str(self.url.content[index][0]))
        self.document.add_image(self.url.content[index][0])

    def add_capture(self, index : int):
        self.document.add_text(self.url.content[index][1])

    def run_web_instr(self, winstr_ctx):
        if winstr_ctx.load_url() != None:
            self.load_url(winstr_ctx.load_url())
        elif winstr_ctx.loop() != None:
            self.run_loop(winstr_ctx.loop())

    def load_url(self, url_ctx):
        # url seems like 'http://...' with quotes
        self.url = UrlExecutor(url=str(url_ctx.getText()[1:-1]))

    def run_loop(self, loop_ctx):
        begin = 0
        end   = len(self.url.content)
        if loop_ctx.in_range() != None:
            rng = loop_ctx.in_range()
            begin = int(rng.Number(0).getText())
            end   = int(rng.Number(1).getText())
        
        for i in range(begin, end):
            self.run_loop_block(loop_ctx.loop_block(), i)

        self.cur_url_index = 0
        
    def run_loop_block(self, block_ctx, iter_num):
        instrs = block_ctx.docx_instr_semi()
        for instr in instrs:
            if instr.docx_instr() != None:
                self.run_docx_instr(instr.docx_instr(), iter_num)



if __name__ == '__main__':
    r = Runner(sys.argv[1])
    r.run()