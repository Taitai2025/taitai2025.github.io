"""Mark the first page of a publicly distributed working copy."""
from pathlib import Path
import sys
import pymupdf

NOTICE="AI-assisted working paper. Author verification pending."

def mark(source, output):
    with pymupdf.open(source) as doc:
        page=doc[0]
        x0,y0,x1,y1=page.rect
        strip=pymupdf.Rect(x0+63,y0+42,x1-63,y0+64)
        assert all(not strip.intersects(pymupdf.Rect(*b[:4])) for b in page.get_text("blocks")), "Title-page margin is occupied"
        progress=page.insert_textbox(strip,NOTICE,fontsize=10,fontname="heit",align=1,color=(.13,.24,.38))
        if progress < 0:
            raise ValueError("The review notice does not fit")
        meta=doc.metadata
        meta.update({"author":"","subject":NOTICE})
        doc.set_metadata(meta)
        doc.save(output,garbage=3,deflate=True)
    with pymupdf.open(source) as before,pymupdf.open(output) as after:
        assert len(before)==len(after)
        assert all(p.get_text()==q.get_text() for p,q in zip(list(before)[1:],list(after)[1:]))
        assert after[0].get_text().replace(NOTICE+"\n","")==before[0].get_text()
        assert after.metadata["author"]==""

if __name__=="__main__":
    source,output=map(Path,sys.argv[1:])
    if source.resolve()==output.resolve():
        raise ValueError("Use a separate output copy")
    mark(source,output)

