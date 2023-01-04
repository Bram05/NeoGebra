#include "ButtonUI.h"
#include "Renderer.h"
#include "Application.h"

ButtonUI::ButtonUI(double leftX, double rightX, double topY, double bottomY, void(*func)(void*), void* obj, const std::string& text)
	: ButtonUI(leftX, rightX, topY, bottomY, func, obj, std::vector<int>(text.begin(), text.end())) {}

ButtonUI::ButtonUI(double leftX, double rightX, double topY, double bottomY, void(*func)(void*), void* obj, const std::vector<int>& text)
	: UIElement(leftX, rightX, topY, bottomY, "ButtonUI"),
	m_Background(std::make_shared<Square>(leftX, rightX, topY, bottomY, std::array{ 0.0f, 0.6f, 1.0f, 1.0f })),
	m_Obj(obj)
{
	m_Action = func;
	m_Texts.push_back(std::make_shared<Text>(text, leftX + 0.005f, rightX, bottomY + 0.04f, 36));
}

ButtonUI::~ButtonUI()
{
}

void ButtonUI::RenderPass(Renderer* r)
{
	r->AddToRenderQueue(m_Background);
	for (std::shared_ptr<Text>& text : m_Texts)
	{
		r->AddToRenderQueue(text);
	}
	UIElement::RenderPass(r);
}

void ButtonUI::WasClicked(float x, float y)
{
	if (m_Action)
		m_Action(m_Obj);
}

void ButtonUI::IsHovered(float x, float y)
{
	m_Background->m_Colour = { 0.2f, 0.8f, 1.0f, 1.0f };
}

void ButtonUI::NotHoveredAnymore()
{
	m_Background->m_Colour = { 0.0f, 0.6f, 1.0f, 1.0f };
}
