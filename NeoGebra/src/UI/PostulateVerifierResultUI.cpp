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

static void CheckPostuateI2(PostulateVerifierResultUI* ui, uint64_t count)
{
	UserInput(PostulateVerifierValues output = PostulateVerifier::I2(*Application::Get()->GetModel());
	if (count == ui->m_Count)
		ui->m_I2->SetResult(output));
}
static void CheckPostuateI3(PostulateVerifierResultUI* ui, uint64_t count)
{
	UserInput(PostulateVerifierValues output = PostulateVerifier::I3(*Application::Get()->GetModel());
	if (count == ui->m_Count)
		ui->m_I3->SetResult(output));
}
static void CheckPostuateB1(PostulateVerifierResultUI* ui, uint64_t count)
{
	UserInput(PostulateVerifierValues output = PostulateVerifier::B1(*Application::Get()->GetModel());
	if (count == ui->m_Count)
		ui->m_B1->SetResult(output));
}
static void CheckPostuateB2(PostulateVerifierResultUI* ui, uint64_t count)
{
	UserInput(PostulateVerifierValues output = PostulateVerifier::B2(*Application::Get()->GetModel());
	if (count == ui->m_Count)
		ui->m_B2->SetResult(output));
}
static void CheckPostuateB3(PostulateVerifierResultUI* ui, uint64_t count)
{
	UserInput(PostulateVerifierValues output = PostulateVerifier::B3(*Application::Get()->GetModel());
	if (count == ui->m_Count)
		ui->m_B3->SetResult(output));
}
static void CheckPostuateC3(PostulateVerifierResultUI* ui, uint64_t count)
{
	UserInput(PostulateVerifierValues output = PostulateVerifier::C3(*Application::Get()->GetModel());
	if (count == ui->m_Count)
		ui->m_C3->SetResult(output));
}
static void CheckPostuateDistance(PostulateVerifierResultUI* ui, uint64_t count)
{
	UserInput(PostulateVerifierValues output = PostulateVerifier::DISTANCE(*Application::Get()->GetModel());
	if (count == ui->m_Count)
		ui->m_Distance->SetResult(output));
}
static void CheckPostuateParallel(PostulateVerifierResultUI* ui, uint64_t count)
{
	UserInput(ParallelType output = PostulateVerifier::PARALLEL(*Application::Get()->GetModel());
	if (count == ui->m_Count)
		ui->m_Parallel->SetResult(output));
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

	m_Distance = std::make_shared<PostulateResult>(leftX + 0.01f, rightX - 0.01f, topY - 0.90f, topY - 0.97f, AdvancedString("Distance"));
	m_Parallel = std::make_shared<PostulateResult>(leftX + 0.01f, rightX - 0.01f, topY - 1.03f, topY - 1.10f, AdvancedString("Parallel"));
}

PostulateVerifierResultUI::~PostulateVerifierResultUI()
{
}

void PostulateVerifierResultUI::VerifyPostulates()
{
	++m_Count;
	m_I2->SetResult(BEINGTESTED);
	m_I3->SetResult(BEINGTESTED);
	m_B1->SetResult(BEINGTESTED);
	m_B2->SetResult(BEINGTESTED);
	m_B3->SetResult(BEINGTESTED);
	m_C3->SetResult(BEINGTESTED);
	m_Distance->SetResult(BEINGTESTED);
	m_Parallel->SetResult(BEINGTESTED);

	std::thread(CheckPostuateI2, this, m_Count).detach();
	std::thread(CheckPostuateI3, this, m_Count).detach();
	std::thread(CheckPostuateB1, this, m_Count).detach();
	std::thread(CheckPostuateB2, this, m_Count).detach();
	std::thread(CheckPostuateB3, this, m_Count).detach();
	std::thread(CheckPostuateC3, this, m_Count).detach();
	std::thread(CheckPostuateDistance, this, m_Count).detach();
	std::thread(CheckPostuateParallel, this, m_Count).detach();
}

void PostulateVerifierResultUI::RenderPass(Renderer* r)
{
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
	m_Distance->RenderPass(r);
	m_Parallel->RenderPass(r);
	UIElement::RenderPass(r);
}
