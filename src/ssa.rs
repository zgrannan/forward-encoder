pub type SsaVersion = usize;

use prusti_rustc_interface::{
    index::vec::IndexVec,
    middle::ty,
    middle::mir,
    span::def_id::DefId,
};
use std::collections::HashMap;


#[derive(Debug)]
pub struct SsaUpdate {
    local: mir::Local,
    old_version: SsaVersion,
    new_version: SsaVersion,
}

#[derive(Debug)]
pub struct SsaPhi {
    pub local: mir::Local,
    pub new_version: SsaVersion,
    pub sources: Vec<(mir::BasicBlock, SsaVersion)>,
}

#[derive(Debug)]
pub struct SsaAnalysis {
    pub version: HashMap<(mir::Location, mir::Local), SsaVersion>,
    pub updates: HashMap<mir::Location, SsaUpdate>,
    pub phi: HashMap<mir::BasicBlock, Vec<SsaPhi>>,
}
pub struct SsaVisitor {
    version_counter: IndexVec<mir::Local, SsaVersion>,
    last_version: IndexVec<mir::Local, SsaVersion>,
    block_started: Vec<bool>,
    initial_version_in_block: Vec<Option<IndexVec<mir::Local, SsaVersion>>>,
    final_version_in_block: Vec<Option<IndexVec<mir::Local, SsaVersion>>>,
    local_count: usize,

    pub analysis: SsaAnalysis,
}

impl SsaVisitor
{
    pub fn new(local_count: usize) -> Self {
        Self {
            version_counter: IndexVec::from_raw(vec![0; local_count]),
            last_version: IndexVec::from_raw(vec![0; local_count]),
            block_started: vec![],
            initial_version_in_block: vec![],
            final_version_in_block: vec![],
            local_count,

            analysis: SsaAnalysis {
                version: HashMap::new(),
                updates: HashMap::new(),
                phi: HashMap::new(),
            },
        }
    }

    // TODO: merge with new ...
    pub fn analyse<'a, 'tcx>(&mut self, body: &'a mir::Body<'tcx>) {
        for block in body.basic_blocks.postorder() {
            self.block_started.push(false);
            self.initial_version_in_block.push(None);
            self.final_version_in_block.push(None);
        }
        self.walk_block(body, 0usize.into());
    }

    fn walk_block<'a, 'tcx>(
        &mut self,
        body: &'a mir::Body<'tcx>,
        block: mir::BasicBlock,
    ) {
        if self.final_version_in_block[block.as_usize()].is_some() {
            return;
        }
        if self.block_started[block.as_usize()] {
            panic!("cycle in cfg!");
        }

        self.block_started[block.as_usize()] = true;

        let mut initial_versions = IndexVec::new();
        let mut phis = vec![];
        for local in 0..self.local_count {
            let mut prev_versions: Vec<(
                mir::BasicBlock, // origin
                SsaVersion,
            )> = vec![];
            for pred in &body.basic_blocks.predecessors()[block] { // TODO: iterator
                self.walk_block(body, *pred);
                // TODO: cfg cycles
                prev_versions.push((
                    *pred,
                    self.final_version_in_block[pred.as_usize()].as_ref().unwrap()[local.into()],
                ));
            }
            if prev_versions.is_empty() {
                initial_versions.push(0usize);
            } else {
                if prev_versions.iter().all(|v| v.1 == prev_versions[0].1) {
                    initial_versions.push(prev_versions[0].1);
                } else {
                    let new_version = self.last_version[local.into()] + 1;
                    self.last_version[local.into()] = new_version;
                    phis.push(SsaPhi {
                        local: local.into(),
                        new_version,
                        sources: prev_versions,
                    });
                    initial_versions.push(new_version);
                }
            }
        }
        if !phis.is_empty() {
            assert!(self.analysis.phi.insert(block, phis).is_none());
        }

        assert!(self.initial_version_in_block[block.as_usize()].replace(initial_versions.clone()).is_none());

        use mir::visit::Visitor;
        self.last_version = initial_versions;
        self.visit_basic_block_data(block, &body[block]);

        let final_versions = (0..self.local_count)
            .map(|local| self.last_version[local.into()])
            .collect::<IndexVec<_, _>>();
        for local in 0..self.local_count {
            self.analysis.version.insert((
                body.terminator_loc(block),
                local.into(),
            ), final_versions[local.into()]);
        }
        assert!(self.final_version_in_block[block.as_usize()].replace(final_versions).is_none());

        use prusti_rustc_interface::data_structures::graph::WithSuccessors;
        for succ in body.basic_blocks.successors(block) {
            if !self.block_started[succ.as_usize()] {
                self.walk_block(body, succ);
            }
        }
    }
}

impl<'tcx> mir::visit::Visitor<'tcx> for SsaVisitor {
    fn visit_place(
        &mut self,
        place: &mir::Place<'tcx>,
        context: mir::visit::PlaceContext,
        location: mir::Location,
    ) {
        // eprintln!(" ssa: {place:?} {context:?} {location:?}");
        if !place.projection.is_empty() {
            return;
        }
        let local = place.local;

        if let mir::visit::PlaceContext::MutatingUse(_) = context {
            let old_version = self.last_version[local];
            let new_version = self.version_counter[local] + 1;
            self.version_counter[local] = new_version;
            self.last_version[local] = new_version;
            assert!(self.analysis.updates
                .insert(location, SsaUpdate {
                    local,
                    old_version,
                    new_version,
                })
                .is_none());
        }

        assert!(self.analysis.version
            .insert((location, local), self.last_version[local])
            .is_none());
    }
}