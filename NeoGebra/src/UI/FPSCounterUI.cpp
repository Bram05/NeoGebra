#include "FPSCounterUI.h"
#include "Rendering/Renderer.h"

FPSCounterUI::FPSCounterUI(float leftX, float rightX, float topY, float bottomY)
	: UIElement(leftX, rightX, topY, bottomY, "FPSCounter"), m_Text(std::make_shared<Text>("----", leftX, rightX, bottomY + 0.08f, 60.0f))
{
}

void FPSCounterUI::SetCounter(float fps)
{
	m_Text->SetText(std::to_string(fps));
}

void FPSCounterUI::RenderPass(Renderer* r)
{
	r->AddToRenderQueue(m_Text);
}