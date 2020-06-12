from __future__ import absolute_import
from __future__ import division
from __future__ import print_function

from rdflib.store import Store, NO_STORE, VALID_STORE

from collections import OrderedDict
from orderedset import OrderedSet
from rdflib.plugins.memory import IOMemory
from rdflib.plugins.memory import randid


class SortedIOMemory(IOMemory):
    """\
            A sorted triples flavor of the IOMemory
    """
    context_aware = True
    formula_aware = True
    graph_aware = True

    # The following variable name conventions are used in this class:
    #
    # subject, predicate, object             unencoded triple parts
    # triple = (subject, predicate, object)  unencoded triple
    # context:                               unencoded context
    #
    # sid, pid, oid                          integer-encoded triple parts
    # enctriple = (sid, pid, oid)            integer-encoded triple
    # cid                                    integer-encoded context

    def __init__(self, configuration=None, identifier=None):
        IOMemory.__init__(self, configuration, identifier)
        self.__namespace = OrderedDict() #{}
        self.__prefix = OrderedDict() #{}

        # Mappings for encoding RDF nodes using integer keys, to save memory
        # in the indexes Note that None is always mapped to itself, to make
        # it easy to test for it in either encoded or unencoded form.
        #self.__int2obj = {None: None}  # maps integer keys to objects
        #self.__obj2int = {None: None}  # maps objects to integer keys
        self.__int2obj = OrderedDict()
        self.__int2obj[None] = None
        self.__obj2int = OrderedDict()
        self.__obj2int[None] = None
 

        # Indexes for each triple part, and a list of contexts for each triple
        self.__subjectIndex = OrderedDict() #{}    # key: sid    val: set(enctriples)
        self.__predicateIndex = OrderedDict() #{}  # key: pid    val: set(enctriples)
        self.__objectIndex = OrderedDict() #{}     # key: oid    val: set(enctriples)
        self.__tripleContexts = OrderedDict() #{}  # key: enctriple    val: {cid1: quoted, cid2: quoted ...}
        #self.__contextTriples = {None: set()}  # key: cid    val: set(enctriples)
        self.__contextTriples = OrderedDict()
        self.__contextTriples[None] = OrderedSet()

        # all contexts used in store (unencoded)
        self.__all_contexts = OrderedSet() #set()
        # default context information for triples
        self.__defaultContexts = None

    def add(self, triple, context, quoted=False):
        Store.add(self, triple, context, quoted)

        if context is not None:
            self.__all_contexts.add(context)

        enctriple = self.__encodeTriple(triple)
        sid, pid, oid = enctriple

        self.__addTripleContext(enctriple, context, quoted)

        if sid in self.__subjectIndex:
            self.__subjectIndex[sid].add(enctriple)
        else:
            self.__subjectIndex[sid] = OrderedSet([enctriple])

        if pid in self.__predicateIndex:
            self.__predicateIndex[pid].add(enctriple)
        else:
            self.__predicateIndex[pid] = OrderedSet([enctriple])

        if oid in self.__objectIndex:
            self.__objectIndex[oid].add(enctriple)
        else:
            self.__objectIndex[oid] = OrderedSet([enctriple])

    def remove(self, triplepat, context=None):
        req_cid = self.__obj2id(context)
        for triple, contexts in self.triples(triplepat, context):
            enctriple = self.__encodeTriple(triple)
            for cid in self.__getTripleContexts(enctriple):
                if context is not None and req_cid != cid:
                    continue
                self.__removeTripleContext(enctriple, cid)
            ctxs = self.__getTripleContexts(enctriple, skipQuoted=True)
            if None in ctxs and (context is None or len(ctxs) == 1):
                self.__removeTripleContext(enctriple, None)
            if len(self.__getTripleContexts(enctriple)) == 0:
                # triple has been removed from all contexts
                sid, pid, oid = enctriple
                self.__subjectIndex[sid].remove(enctriple)
                self.__predicateIndex[pid].remove(enctriple)
                self.__objectIndex[oid].remove(enctriple)

                del self.__tripleContexts[enctriple]

        if not req_cid is None and \
                req_cid in self.__contextTriples and \
                len(self.__contextTriples[req_cid]) == 0:
            # all triples are removed out of this context
            # and it's not the default context so delete it
            del self.__contextTriples[req_cid]

        if triplepat == (None, None, None) and \
                context in self.__all_contexts and \
                not self.graph_aware:
            # remove the whole context
            self.__all_contexts.remove(context)



    def triples(self, triplein, context=None):
        if context is not None:
            if context == self:  # hmm...does this really ever happen?
                context = None

        cid = self.__obj2id(context)
        enctriple = self.__encodeTriple(triplein)
        sid, pid, oid = enctriple

        # all triples case (no triple parts given as pattern)
        if sid is None and pid is None and oid is None:
            return self.__all_triples(cid)

        # optimize "triple in graph" case (all parts given)
        if sid is not None and pid is not None and oid is not None:
            if sid in self.__subjectIndex and \
               enctriple in self.__subjectIndex[sid] and \
               self.__tripleHasContext(enctriple, cid):
                return ((triplein, self.__contexts(enctriple)) for i in [0])
            else:
                return self.__emptygen()

        # remaining cases: one or two out of three given
        sets = []
        if sid is not None:
            if sid in self.__subjectIndex:
                sets.append(self.__subjectIndex[sid])
            else:
                return self.__emptygen()
        if pid is not None:
            if pid in self.__predicateIndex:
                sets.append(self.__predicateIndex[pid])
            else:
                return self.__emptygen()
        if oid is not None:
            if oid in self.__objectIndex:
                sets.append(self.__objectIndex[oid])
            else:
                return self.__emptygen()

        # to get the result, do an intersection of the sets (if necessary)
        if len(sets) > 1:
            enctriples = sets[0].intersection(*sets[1:])
        else:
            enctriples = sets[0].copy()

        #print("context:")
        #print(context)
        #print("triplein:")
        #print(triplein)
        #for enctriple in enctriples:
        #    print("  decodeTriple:")
        #    print(self.__decodeTriple(enctriple))
        #    print("---")

        return ((self.__decodeTriple(enctriple), self.__contexts(enctriple))
                for enctriple in enctriples
                if self.__tripleHasContext(enctriple, cid))

    def contexts(self, triple=None):
        if triple is None or triple == (None, None, None):
            return (context for context in self.__all_contexts)

        enctriple = self.__encodeTriple(triple)
        sid, pid, oid = enctriple
        if sid in self.__subjectIndex and enctriple in self.__subjectIndex[sid]:
            return self.__contexts(enctriple)
        else:
            return self.__emptygen()

    def __len__(self, context=None):
        cid = self.__obj2id(context)
        if cid not in self.__contextTriples:
            return 0
        return len(self.__contextTriples[cid])

    def add_graph(self, graph):
        if not self.graph_aware:
            Store.add_graph(self, graph)
        else:
            self.__all_contexts.add(graph)

    def remove_graph(self, graph):
        if not self.graph_aware:
            Store.remove_graph(self, graph)
        else:
            self.remove((None, None, None), graph)
            try:
                self.__all_contexts.remove(graph)
            except KeyError:
                pass  # we didn't know this graph, no problem

    # internal utility methods below






    # internal utility methods below

    def __addTripleContext(self, enctriple, context, quoted):
        """add the given context to the set of contexts for the triple"""
        cid = self.__obj2id(context)

        sid, pid, oid = enctriple
        if sid in self.__subjectIndex and enctriple in self.__subjectIndex[sid]:
            # we know the triple exists somewhere in the store
            if enctriple not in self.__tripleContexts:
                # triple exists with default ctx info
                # start with a copy of the default ctx info
                self.__tripleContexts[
                    enctriple] = self.__defaultContexts.copy()

            self.__tripleContexts[enctriple][cid] = quoted
            if not quoted:
                self.__tripleContexts[enctriple][None] = quoted
        else:
            # the triple didn't exist before in the store
            if quoted:  # this context only
                self.__tripleContexts[enctriple] = {cid: quoted}
            else:  # default context as well
                self.__tripleContexts[enctriple] = {cid: quoted, None: quoted}

        # if the triple is not quoted add it to the default context
        if not quoted:
            self.__contextTriples[None].add(enctriple)

        # always add the triple to given context, making sure it's initialized
        if cid not in self.__contextTriples:
            self.__contextTriples[cid] = OrderedSet() #set()
        self.__contextTriples[cid].add(enctriple)

        # if this is the first ever triple in the store, set default ctx info
        if self.__defaultContexts is None:
            self.__defaultContexts = self.__tripleContexts[enctriple]

        # if the context info is the same as default, no need to store it
        if self.__tripleContexts[enctriple] == self.__defaultContexts:
            del self.__tripleContexts[enctriple]

    def __getTripleContexts(self, enctriple, skipQuoted=False):
        """return a list of (encoded) contexts for the triple, skipping
           quoted contexts if skipQuoted==True"""

        ctxs = self.__tripleContexts.get(enctriple, self.__defaultContexts)

        if not skipQuoted:
            return ctxs.keys()

        return [cid for cid, quoted in ctxs.items() if not quoted]

    def __tripleHasContext(self, enctriple, cid):
        """return True iff the triple exists in the given context"""
        ctxs = self.__tripleContexts.get(enctriple, self.__defaultContexts)
        return (cid in ctxs)

    def __removeTripleContext(self, enctriple, cid):
        """remove the context from the triple"""
        ctxs = self.__tripleContexts.get(
            enctriple, self.__defaultContexts).copy()
        del ctxs[cid]
        if ctxs == self.__defaultContexts:
            del self.__tripleContexts[enctriple]
        else:
            self.__tripleContexts[enctriple] = ctxs
        self.__contextTriples[cid].remove(enctriple)

    def __obj2id(self, obj):
        """encode object, storing it in the encoding map if necessary,
           and return the integer key"""
        if obj not in self.__obj2int:
            id = randid()
            while id in self.__int2obj:
                id = randid()
            self.__obj2int[obj] = id
            self.__int2obj[id] = obj
            return id
        return self.__obj2int[obj]

    def __encodeTriple(self, triple):
        """encode a whole triple, returning the encoded triple"""
        return tuple(map(self.__obj2id, triple))

    def __decodeTriple(self, enctriple):
        """decode a whole encoded triple, returning the original
        triple"""
        return tuple(map(self.__int2obj.get, enctriple))

    def __all_triples(self, cid):
        """return a generator which yields all the triples (unencoded)
           of the given context"""
        if cid not in self.__contextTriples:
            return
        for enctriple in self.__contextTriples[cid].copy():
            yield self.__decodeTriple(enctriple), self.__contexts(enctriple)

    def __contexts(self, enctriple):
        """return a generator for all the non-quoted contexts
           (unencoded) the encoded triple appears in"""
        return (self.__int2obj.get(cid) for cid in self.__getTripleContexts(enctriple, skipQuoted=True) if cid is not None)

    def __emptygen(self):
        """return an empty generator"""
        if False:
            yield



