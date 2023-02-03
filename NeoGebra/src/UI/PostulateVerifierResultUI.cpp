// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#include "PostulateVerifierResultUI.h"

#include "Application.h"
#include "PostulateResult.h"
#include "Maths/PostulateVerifier.h"

static void CheckPostulates(void* obj)
{
	((PostulateVerifierResultUI*)obj)->VerifyPostulates();
}

PostulateVerifierResultUI::PostulateVerifierResultUI(float leftX, float rightX, float topY, float bottomY)
	: UIElement(leftX, rightX, topY, bottomY, "PostulateVerifierResultUI")
{
	m_Lines.push_back(std::make_shared<Line>(Point(leftX, topY), Point(leftX, bottomY))); // Left size
	m_Lines.push_back(std::make_shared<Line>(Point(leftX, topY), Point(rightX, topY))); // top
	m_Lines.push_back(std::make_shared<Line>(Point(rightX, bottomY), Point(rightX, topY))); // right
	m_Lines.push_back(std::make_shared<Line>(Point(rightX, bottomY), Point(leftX, bottomY))); // bottom
	m_SubUIElements.emplace_back(std::make_shared<ButtonUI>(leftX + 0.04f, rightX - 0.04f, topY - 0.05f, topY - 0.25f, CheckPostulates, this, "Verify Posulates"));
	//m_SubUIElements.emplace_back(std::make_shared<PostulateResult>(leftX + 0.01f, rightX - 0.01f, topY - 0.3f, topY - 0.5f, AdvancedString("I-3")));
	m_I2 = std::make_shared<PostulateResult>(leftX + 0.01f, rightX - 0.01f, topY - 0.3f, topY - 0.37f, AdvancedString("I-2"));
	m_I3 = std::make_shared<PostulateResult>(leftX + 0.01f, rightX - 0.01f, topY - 0.37f, topY - 0.44f, AdvancedString("I-3"));

	m_B1 = std::make_shared<PostulateResult>(leftX + 0.01f, rightX - 0.01f, topY - 0.50f, topY - 0.57f, AdvancedString("B-1"));
	m_B2 = std::make_shared<PostulateResult>(leftX + 0.01f, rightX - 0.01f, topY - 0.57f, topY - 0.64f, AdvancedString("B-2"));
	m_B3 = std::make_shared<PostulateResult>(leftX + 0.01f, rightX - 0.01f, topY - 0.64f, topY - 0.71f, AdvancedString("B-3"));

	m_C3 = std::make_shared<PostulateResult>(leftX + 0.01f, rightX - 0.01f, topY - 0.77f, topY - 0.84f, AdvancedString("C-3"));
	//m_I3, m_B1, m_B2, m_B3, m_C3, m_Distance, m_Parallel
}

PostulateVerifierResultUI::~PostulateVerifierResultUI()
{
}

void PostulateVerifierResultUI::VerifyPostulates()
{
	m_I2->SetResult(BEINGTESTED);
	m_I3->SetResult(BEINGTESTED);
	m_B1->SetResult(BEINGTESTED);
	m_B2->SetResult(BEINGTESTED);
	m_B3->SetResult(BEINGTESTED);
	m_C3->SetResult(BEINGTESTED);
	m_TimesTillVerify = 1;
}

void PostulateVerifierResultUI::RenderPass(Renderer* r)
{
	if (m_TimesTillVerify == 1)
		m_TimesTillVerify = 0;
	else if (m_TimesTillVerify == 0)
	{
		const Model& model = *Application::Get()->GetModel().get();
		UserInput(m_I2->SetResult(PostulateVerifier::I2(model) ? VALID : INVALID));
		UserInput(m_I3->SetResult(PostulateVerifier::I3(model) ? VALID : INVALID));
		UserInput(m_B1->SetResult(PostulateVerifier::B1(model) ? VALID : INVALID));
		UserInput(m_B2->SetResult(PostulateVerifier::B2(model) ? VALID : INVALID));
		UserInput(m_B3->SetResult(PostulateVerifier::B3(model) ? VALID : INVALID));
		UserInput(m_C3->SetResult(PostulateVerifier::C3(model) ? VALID : INVALID));
		m_TimesTillVerify = -1;
	}
	for (std::shared_ptr<Line>& line : m_Lines)
	{
		r->AddToRenderQueue(line);
	}
	m_I2->RenderPass(r);
	m_I3->RenderPass(r);
	m_B1->RenderPass(r);
	m_B2->RenderPass(r);
	m_B3->RenderPass(r);
	m_C3->RenderPass(r);
	UIElement::RenderPass(r);
}
