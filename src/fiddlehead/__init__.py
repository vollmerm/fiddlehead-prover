"""Public package entrypoint for the Fiddlehead prover.

Importing :mod:`fiddlehead` re-exports the stable, user-facing API from
``fiddlehead.prover`` so callers can write concise imports such as
``from fiddlehead import prove, App, Rule``. Advanced names live in the
submodules (``fiddlehead.prover``, ``fiddlehead.syntax``, ...).
"""

from . import prover
from .prover import *

__all__ = list(prover.__all__)
