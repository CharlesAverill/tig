
""" Overwrite PagedMemoryMixin.load to always(?) use symbolic memroy pointers """
from angr.storage.memory_mixins.paged_memory.paged_memory_mixin import PagedMemoryMixin
from angr.storage.memory_mixins.paged_memory.pages.cooperation import SimMemoryObject

orig_load = PagedMemoryMixin.load

def symmem_load(self, addr: int, size: int | None = None, *, endness=None, **kwargs):
    if endness is None:
        endness = self.endness

    if not isinstance(size, int):
        raise TypeError("Need size to be resolved to an int by this point")

    if not isinstance(addr, int):
        raise TypeError("Need addr to be resolved to an int by this point")

    pageno, pageoff = self._divide_addr(addr)

    if kwargs["condition"] is not None:
        cond = kwargs["condition"]
        from claripy.ast.base import Base
        match_mem = False
        for child in cond.children_asts():
            if not isinstance(child.args[0], Base):
                if isinstance(child.args[0], str):
                    if child.args[0].startswith("mem_"):
                        match_mem = True
                        break
        if match_mem:
            page_addr = pageno * self.page_size
            page = self._get_page(pageno, False, **kwargs)
            global_start_addr = page_addr + addr + size
            new_ast = self._default_value(
                global_start_addr,
                size,  # pylint: disable=assignment-from-no-return
                key=(self.category, global_start_addr),
                memory=self,
                endness=endness,
                **kwargs,
            )
            new_item = SimMemoryObject(new_ast, global_start_addr, endness=endness)
            page.symbolic_data[global_start_addr - page_addr] = new_item
            out = self.PAGE_TYPE._compose_objects([[(global_start_addr, new_item)]], size, endness, memory=self, **kwargs)
            return out
    return orig_load(self, addr=addr, size=size, **kwargs)

PagedMemoryMixin.load = symmem_load


""" Overwrite Pcode's clz handler """
from angr.engines.pcode.behavior import OpBehaviorLzcount
from claripy.ast.bv import BV, BVS

orig_evaluate_unary = OpBehaviorLzcount.evaluate_unary

def sym_eval_lzcount(self, size_out: int, size_in: int, in1: BV) -> BV:
    extracted_expr,_ = in1.args
    return BVS("CLZ_{"+extracted_expr+"}", size_out * 8)

OpBehaviorLzcount.evaluate_unary = sym_eval_lzcount
