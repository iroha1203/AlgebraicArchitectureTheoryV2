#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TraceEvent {
    pub stage: String,
    pub detail: String,
}

impl TraceEvent {
    pub fn new(stage: impl Into<String>, detail: impl Into<String>) -> Self {
        Self {
            stage: stage.into(),
            detail: detail.into(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct TraceRecorder {
    component: String,
    events: Vec<TraceEvent>,
}

impl TraceRecorder {
    pub fn new(component: impl Into<String>) -> Self {
        Self {
            component: component.into(),
            events: Vec::new(),
        }
    }

    pub fn record(&mut self, stage: impl Into<String>, detail: impl Into<String>) {
        self.events.push(TraceEvent::new(
            format!("{}:{}", self.component, stage.into()),
            detail,
        ));
    }

    pub fn events(&self) -> &[TraceEvent] {
        &self.events
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PresentationSnapshot {
    pub title: String,
    pub insight_lines: Vec<String>,
}

impl PresentationSnapshot {
    pub fn new(title: impl Into<String>) -> Self {
        Self {
            title: title.into(),
            insight_lines: Vec::new(),
        }
    }

    pub fn push(&mut self, line: impl Into<String>) {
        self.insight_lines.push(line.into());
    }

    pub fn render(&self) -> String {
        let mut output = self.title.clone();
        for line in &self.insight_lines {
            output.push('\n');
            output.push_str("- ");
            output.push_str(line);
        }
        output
    }
}
